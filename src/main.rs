use std::process::ExitCode;

fn main() -> ExitCode {
    match mathmux::cli::run() {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("error: {error:#}");
            ExitCode::FAILURE
        }
    }
}
