use std::fs::{self, File};
use std::path::Path;
use std::sync::{Mutex, MutexGuard, TryLockError};
use std::time::{Duration, Instant};

use anyhow::Result;
use fs2::FileExt;

const POLL_INTERVAL: Duration = Duration::from_millis(50);

pub(crate) fn open_lock(path: &Path) -> Result<File> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    Ok(fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(path)?)
}

pub(crate) fn lock_mutex_until<'a, T>(
    lock: &'a Mutex<T>,
    timeout: Duration,
) -> Result<MutexGuard<'a, T>> {
    let deadline = Instant::now() + timeout;
    loop {
        match lock.try_lock() {
            Ok(guard) => return Ok(guard),
            Err(TryLockError::WouldBlock) if Instant::now() < deadline => pause(timeout),
            Err(TryLockError::WouldBlock) => anyhow::bail!("lock wait timed out"),
            Err(TryLockError::Poisoned(_)) => anyhow::bail!("lock is poisoned"),
        }
    }
}

pub(crate) fn lock_exclusive_until(file: &File, timeout: Duration) -> Result<()> {
    let deadline = Instant::now() + timeout;
    loop {
        match FileExt::try_lock_exclusive(file) {
            Ok(()) => return Ok(()),
            Err(error)
                if error.kind() == std::io::ErrorKind::WouldBlock && Instant::now() < deadline =>
            {
                pause(timeout);
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                anyhow::bail!("lock wait timed out")
            }
            Err(error) => return Err(error.into()),
        }
    }
}

pub(crate) fn lock_exclusive(file: &File) -> Result<()> {
    FileExt::lock_exclusive(file)?;
    Ok(())
}

fn pause(timeout: Duration) {
    std::thread::sleep(POLL_INTERVAL.min(timeout));
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn mutex_wait_is_bounded() {
        let lock = Mutex::new(());
        let _guard = lock.lock().unwrap();
        assert!(lock_mutex_until(&lock, Duration::from_millis(5)).is_err());
    }

    #[test]
    fn process_lock_wait_is_bounded() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("coordination.lock");
        let owner = open_lock(&path).unwrap();
        owner.lock_exclusive().unwrap();
        let waiter = open_lock(&path).unwrap();
        assert!(lock_exclusive_until(&waiter, Duration::from_millis(5)).is_err());
    }
}
