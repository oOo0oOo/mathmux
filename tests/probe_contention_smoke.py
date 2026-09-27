"""A busy probe returns promptly without interrupting a check. Args: binary, lean."""
import concurrent.futures, json, os, pathlib, shutil, sqlite3, subprocess, sys, tempfile, time
binary = str(pathlib.Path(sys.argv[1]).resolve())
leanbin = pathlib.Path(sys.argv[2]).resolve().parent
with tempfile.TemporaryDirectory(prefix='mathmux-probe-busy-') as tmp:
    root = pathlib.Path(tmp) / 'repo'; root.mkdir()
    env = {**os.environ, 'PATH': str(leanbin)+os.pathsep+os.environ['PATH'],
           'MATHMUX_ISSUE_DB': str(pathlib.Path(tmp)/'telemetry.db'), 'MATHMUX_IDLE_SECONDS': '2'}
    def run(args, cwd=root, ok=True):
        p = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=60)
        if ok: assert p.returncode == 0, (args,p.stdout,p.stderr)
        return p
    run(['git','init','-b','main']); run(['git','config','user.name','Test']); run(['git','config','user.email','test@example.invalid'])
    version=run([str(leanbin/'lean'),'--version']).stdout.split('version ')[1].split()[0].rstrip(',')
    (root/'lean-toolchain').write_text('leanprover/lean4:v'+version+'\n')
    (root/'lakefile.toml').write_text('name = "busy"\n[[lean_lib]]\nname = "Fixture"\n')
    marker=pathlib.Path(tmp)/'started'
    (root/'Fixture.lean').write_text('import Lean\n#eval do\n  IO.FS.writeFile '+json.dumps(str(marker))+' "ready"\n  IO.sleep 8000\ntheorem target : True := True.intro\n')
    run(['git','add','.']); run(['git','commit','-m','fixture'])
    log=open(pathlib.Path(tmp)/'daemon.log','w+')
    daemon=subprocess.Popen([binary,'__daemon','--repo',str(root)],env=env,stdout=log,stderr=log)
    check=None; sibling=root.parent/('.mathmux-'+root.name)
    try:
        deadline=time.monotonic()+15
        while not (root/'.git/mathmux/daemon.sock').exists() and time.monotonic()<deadline:
            assert daemon.poll() is None
            time.sleep(.02)
        run([binary,'ws','create','smoke'])
        db=sqlite3.connect(root/'.git/mathmux/state.sqlite3')
        ws=pathlib.Path(db.execute('select path from workspaces where deleted_at is null').fetchone()[0]); db.close()
        check=subprocess.Popen([binary,'check','Fixture.lean'],cwd=ws,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        deadline=time.monotonic()+30
        while not marker.exists() and time.monotonic()<deadline:
            assert check.poll() is None
            time.sleep(.02)
        assert marker.exists(), 'check did not enter worker'
        started=time.monotonic()
        with concurrent.futures.ThreadPoolExecutor(3) as pool:
            probes=list(pool.map(lambda term: run([binary,'probe','Fixture.lean #check '+term],ws,ok=False), ['Nat','Bool','String']))
        elapsed=time.monotonic()-started
        for probe in probes:
            assert probe.returncode != 0 and 'probe busy (not queued)' in probe.stderr, (elapsed,probe.stdout,probe.stderr)
            assert 'Fixture.lean' in probe.stderr and 'No probe was executed' in probe.stderr, probe.stderr
            assert 'infrastructure failure' not in probe.stderr and 'lock wait timed out' not in probe.stderr, probe.stderr
        assert elapsed<4, elapsed
        assert check.poll() is None, 'active check was interrupted or probe waited for completion'
        with sqlite3.connect(env['MATHMUX_ISSUE_DB']) as telemetry:
            busy=telemetry.execute("SELECT outcome_class,error_class,attempt_id FROM telemetry_events WHERE verb='probe'").fetchall()
        assert len(busy)==3 and all(row[:2]==('busy','busy') for row in busy), busy
        assert len(set(row[2] for row in busy))==3, busy
        out,err=check.communicate(timeout=30)
        assert check.returncode==0,(out,err)
        assert 'Nat' in run([binary,'probe','Fixture.lean #check Nat'],ws).stdout
        print('Three concurrent probes returned explicit busy outcomes; active check preserved; subsequent sequential probe passed')
    finally:
        if check is not None and check.poll() is None: check.communicate(timeout=30)
        try: daemon.wait(timeout=15)
        except subprocess.TimeoutExpired: daemon.terminate(); daemon.wait(timeout=5)
        log.close()
        if sibling.exists(): shutil.rmtree(sibling)
