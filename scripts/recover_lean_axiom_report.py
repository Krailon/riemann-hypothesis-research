#!/usr/bin/env python3
"""Recover this milestone's final report after its missing RHS import.

Reuse comparison evidence only when every recorded proof/configuration/tool and
actual dependency diff is identical. The sole allowed old-source change is the
addition of the RHS module import to AxiomReport.lean. Preserve the failed run.
For an ordinary complete reproduction use reproduce_lean.py.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

from bootstrap_lean import ROOT, environment
from reproduce_lean import digest, source_hashes


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    previous = Path(sys.argv[1]).resolve()
    old = json.loads(previous.read_text())
    previous_hash = digest(previous)
    require(previous.parent.name == previous_hash, 'previous manifest hash mismatch')
    require(old['status'] == 'fail' and old['commands'][-1]['name'] == 'axioms'
            and old['commands'][-1]['exit_code'] != 0, 'not the expected final-report failure')
    current = source_hashes()
    report_path = 'lean/HigherCorrelations/AxiomReport.lean'
    prefix = b'import HigherCorrelations.PairRHSMean\n'
    source = (ROOT / report_path).read_bytes()
    require(source.startswith(prefix), 'missing repaired import')
    require(hashlib.sha256(source[len(prefix):]).hexdigest() == old['source_hashes'][report_path],
            'axiom report changed beyond the single import')
    require(current.keys() == old['source_hashes'].keys(), 'source inventory changed')
    for path, sha in old['source_hashes'].items():
        require(path == report_path or current[path] == sha, 'changed source: ' + path)
    for path, sha in old['outputs'].items():
        require(digest(previous.parent / path) == sha, 'changed evidence: ' + path)
    for path, sha in old['tool_binary_hashes'].items():
        require(digest(ROOT / path) == sha, 'changed tool: ' + path)
    for path, sha in old['upstream_patch_hashes'].items():
        require(digest(ROOT / '.lake/packages/OAI/lean/patches' / path) == sha, 'changed patch: ' + path)
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())
    by_name = {p['name'].strip('«»'): p for p in packages['packages'] if p['type'] == 'git'}
    for name, evidence in old['dependency_checkouts'].items():
        checkout = ROOT / packages['packagesDir'] / name
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
        require(revision == evidence['rev'] == by_name[name]['rev'], 'changed dependency pin: ' + name)
        diff = subprocess.check_output(['git', 'diff', '--binary', 'HEAD', '--'], cwd=checkout)
        require(hashlib.sha256(diff).hexdigest() == evidence['tracked_diff_sha256'],
                'changed dependency source: ' + name)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    require(commit == old['source_commit'], 'project commit changed')
    for cmd in old['commands'][:-1]:
        log = (previous.parent / cmd['log']).read_text()
        require((cmd['exit_code'] != 0 and "Illegal axiom detected: 'sorryAx'" in log)
                if cmd['expected_failure'] else cmd['exit_code'] == 0,
                'unsuccessful reusable command: ' + cmd['name'])
    require('Lean default kernel accepts the solution' in
            (previous.parent / 'pair-rhs-mean-comparator.log').read_text(), 'missing RHS comparison')

    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run = ROOT / 'artifacts/lean-runs' / (stamp + '-report-recovery')
    run.mkdir(parents=True)
    for name in old['outputs']:
        if name != 'axioms.log':
            shutil.copyfile(previous.parent / name, run / name)
    shutil.copyfile(previous, run / 'previous-failed-manifest.json')
    report = dict(old)
    report.pop('error', None)
    report.update(status='running', started_utc=stamp,
        verification_mode='Verified unchanged comparison evidence plus repaired final axiom report and regressions',
        previous_failed_run=dict(manifest=str(previous.relative_to(ROOT)), sha256=previous_hash),
        permitted_source_changes={report_path: 'Added only import HigherCorrelations.PairRHSMean'},
        commands=[dict(c, evidence_reused_from=previous_hash) for c in old['commands'][:-1]])
    recovery_path = 'scripts/recover_lean_axiom_report.py'
    current[recovery_path] = digest(ROOT / recovery_path)
    report['source_hashes'] = current

    def command(name, argv):
        print(name, flush=True)
        with (run / (name + '.log')).open('w') as out:
            result = subprocess.run(argv, cwd=ROOT, env=environment(), stdout=out, stderr=subprocess.STDOUT)
        report['commands'].append(dict(name=name, argv=argv, exit_code=result.returncode,
                                       log=name + '.log', expected_failure=False))
        require(result.returncode == 0, name + ' failed')
        return (run / (name + '.log')).read_text()

    try:
        axioms = command('axioms', ['lake', 'env', 'lean', report_path])
        entries = re.findall(r"'(\S+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", axioms)
        expected = re.findall(r'^#print axioms (\S+)$', source.decode(), re.M)
        require(len(entries) == len(expected) == len(set(expected)) and
                {n for n, _ in entries} == set(expected), 'axiom reports missing or duplicated')
        require(all(set(re.findall(r'[\w.]+', a)) <= {'propext', 'Quot.sound', 'Classical.choice'}
                    for _, a in entries), 'unapproved axiom')
        command('recovery-coverage', [sys.executable, '-B', 'scripts/check_lean_analytic_coverage.py'])
        command('pair-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                    '-s', 'scripts', '-p', 'check_pair_*.py'])
        command('triple-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                      '-s', 'scripts', '-p', 'check_triple_*.py'])
        now = source_hashes()
        now[recovery_path] = digest(ROOT / recovery_path)
        require(now == current, 'sources changed during recovery')
        report['status'] = 'pass'
    except Exception as exc:
        report.update(status='fail', error=str(exc))
        print(exc, file=sys.stderr)
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        report['outputs'] = {p.name: digest(p) for p in sorted(run.iterdir()) if p.is_file()}
        raw = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
        (run / 'manifest.json').write_bytes(raw)
        target = ROOT / 'artifacts/certificates/lean' / hashlib.sha256(raw).hexdigest()
        shutil.copytree(run, target)
        print('Report:', target / 'manifest.json', flush=True)
    return 0 if report['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
