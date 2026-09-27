"""Isolated regression for issue report --ref eREF. Argument: development binary."""
import json, os, pathlib, sqlite3, subprocess, sys, tempfile
binary = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory(prefix='mathmux-event-issue-') as tmp:
    root = pathlib.Path(tmp)
    dbpath = root / 'development.sqlite3'
    env = {**os.environ, 'MATHMUX_ISSUE_DB': str(dbpath)}
    def run(*args, ok=True):
        result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True, timeout=30)
        if ok:
            assert result.returncode == 0, (args, result.stdout, result.stderr)
        return result
    run('git', 'init', '-b', 'main')
    run('git', 'config', 'user.name', 'Test')
    run('git', 'config', 'user.email', 'test@example.invalid')
    (root / 'Fixture.lean').write_text('theorem fixture : True := True.intro\n')
    run('git', 'add', 'Fixture.lean')
    run('git', 'commit', '-m', 'fixture')
    run(binary, 'dev', 'telemetry')
    db = sqlite3.connect(dbpath)
    db.execute('''INSERT INTO telemetry_events(created_at,build,project,verb,ok,client_ms,daemon_ms,
                  request_bytes,response_bytes,request_json,response_json)
                  VALUES(1,'test',?,'probe',0,30,29,2,80,'{}',?)''',
               (str(root), json.dumps({'summary': 'unique event failure evidence'})))
    db.commit()
    event = db.execute('SELECT id FROM telemetry_events').fetchone()[0]
    for options in [[], ['--all']]:
        shown = run(binary, 'show', f'e{event}', *options)
        expected = run(binary, 'dev', 'show', f'e{event}', *options)
        assert shown.stdout == expected.stdout and f'e{event} probe' in shown.stdout, shown
        if options:
            assert 'unique event failure evidence' in shown.stdout, shown
    waiting = run(binary, 'show', f'e{event}', '--wait', ok=False)
    assert waiting.returncode != 0 and 'already retained' in waiting.stderr, waiting
    unknown = run(binary, 'show', 'e999999', ok=False)
    assert unknown.returncode != 0 and 'unknown reference' in unknown.stderr, unknown
    reported = run(binary, 'issue', 'report', 'event reference regression', '--ref', f'e{event}')
    context = json.loads(db.execute('SELECT context_json FROM issues').fetchone()[0])
    assert context['related_ref'] == f'e{event}', context
    assert 'unique event failure evidence' in context['related_detail'], context
    missing = run(binary, 'issue', 'report', 'missing event', '--ref', 'e999999', ok=False)
    assert missing.returncode != 0 and 'unknown reference' in missing.stderr, missing
    assert db.execute('SELECT COUNT(*) FROM issues').fetchone()[0] == 1
    db.close()
print('Issue event reference smoke passed')
