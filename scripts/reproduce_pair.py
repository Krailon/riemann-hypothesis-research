#!/usr/bin/env python3
"""Offline pair-baseline reproduction, using installed Python 3.12 and TeX.

Task: verification/exposition. Assumptions: UNCONDITIONAL for exact algebra.
Passing this harness is not independent mathematical verification.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

from pair_normalization import generate, json_text, markdown, validate_sources


ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_hashes(root):
    """Explicit source scope excludes generated artifacts and session files."""
    files = {root / name for name in ('AGENTS.md', 'README.md', '.gitignore', 'LICENSE')}
    for directory, suffixes in [('scripts', {'.py', '.sh'}),
                                ('research', {'.md', '.json', '.yaml', '.bib'}),
                                ('proofs', {'.tex'})]:
        files.update(p for p in (root / directory).rglob('*') if p.suffix in suffixes)
    return {str(p.relative_to(root)): sha256(p) for p in sorted(files) if p.is_file()}


def prepare_output(root, requested):
    base = root / 'artifacts/reproduction'
    if requested is None:
        base.mkdir(parents=True, exist_ok=True)
        return Path(tempfile.mkdtemp(prefix='run-', dir=base))
    out = Path(requested).resolve()
    if out.is_relative_to(root) and not out.is_relative_to(base.resolve()):
        raise ValueError('inside the repository, output must be under artifacts/reproduction/')
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise ValueError(f'output destination is not an empty directory: {out}')
    out.mkdir(parents=True, exist_ok=True)
    return out


def execute(manifest, out, name, command, cwd):
    """Log commands without a shell; retain failed command output."""
    log = out / 'logs' / f'{name}.log'
    log.parent.mkdir(exist_ok=True)
    entry = {'name': name, 'command': list(map(str, command)), 'cwd': str(cwd),
             'log': str(log.relative_to(out)), 'status': 'running'}
    manifest['stages'].append(entry)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['TZ'] = 'UTC'
    env['LC_ALL'] = 'C.UTF-8'
    try:
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                encoding='utf-8', errors='replace',
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.write_text(result.stdout, encoding='utf-8')
        entry['returncode'] = result.returncode
        entry['status'] = 'pass' if result.returncode == 0 else 'fail'
        if result.returncode:
            raise RuntimeError(f'{name} failed ({result.returncode}); see {log}')
        return result.stdout
    except OSError as error:
        log.write_text(str(error) + '\n', encoding='utf-8')
        entry.update(status='fail', error=str(error))
        raise RuntimeError(f'{name} could not start; see {log}') from error


def collect_environment(root, out, manifest, checks_only):
    if sys.version_info[:2] != (3, 12):
        raise RuntimeError('Python 3.12 is required; use an installed Python 3.12 interpreter')
    git = shutil.which('git')
    if not git:
        raise RuntimeError('missing prerequisite: git')
    manifest['environment']['git'] = execute(
        manifest, out, 'git-version', [git, '--version'], root).strip()
    commit = execute(manifest, out, 'source-commit', [git, 'rev-parse', 'HEAD'], root).strip()
    status = execute(manifest, out, 'source-status',
                     [git, 'status', '--porcelain=v1', '--untracked-files=all'], root)
    manifest['source'].update(commit=commit, dirty=bool(status.strip()),
                              git_status=status.splitlines())
    tools = {}
    if not checks_only:
        for name in ('pdflatex', 'bibtex'):
            executable = shutil.which(name)
            if not executable:
                raise RuntimeError(f'missing prerequisite: {name}; install TeX or use --checks-only')
            tools[name] = executable
            version = execute(manifest, out, f'{name}-version', [executable, '--version'], root)
            manifest['environment'][name] = {'executable': executable, 'version': version.strip()}
    return tools


def check_test_log(output):
    match = re.search(r'^Ran (\d+) tests? in ', output, re.M)
    if not match or int(match[1]) < 59 or not re.search(r'^OK\s*$', output, re.M):
        raise RuntimeError('test discovery did not report at least 59 tests and an unqualified OK')
    return int(match[1])


def run_checks(root, out, manifest):
    print('Running exact regression and audit checks...', flush=True)
    manifest['tests'] = {'status': 'running'}
    try:
        output = execute(manifest, out, 'checks',
                         [sys.executable, '-B', '-m', 'unittest', 'discover',
                          '-s', 'scripts', '-p', 'check_pair_*.py', '-v'], root)
        count = check_test_log(output)
        manifest['tests'] = {'status': 'pass', 'run': count, 'failures': 0, 'errors': 0, 'skipped': 0}
    except RuntimeError as error:
        manifest['tests'] = {'status': 'fail', 'error': str(error)}
        raise


def tex_diagnostics(text):
    failures, warnings = [], []
    for line in text.splitlines():
        warning = 'Warning' in line
        continuation = re.match(r'^\([\w-]+\)\s+', line)
        if (warning or continuation) and re.search(
                r'undefined|\brerun\b|Label\(s\) may have changed|multiply defined',
                line, re.I):
            failures.append(line)
        elif warning or 'Overfull' in line or 'Underfull' in line:
            warnings.append(line)
    return failures, warnings


def build_pdf(root, out, manifest, tools):
    print('Building the pair manuscript...', flush=True)
    build = out / 'build'
    (build / 'proofs').mkdir(parents=True)
    (build / 'research').mkdir()
    shutil.copy2(root / 'proofs/pair_baseline.tex', build / 'proofs')
    shutil.copy2(root / 'research/literature.bib', build / 'research')
    tex = [tools['pdflatex'], '-no-shell-escape', '-interaction=nonstopmode',
           '-halt-on-error', '-file-line-error', 'pair_baseline.tex']
    for name, command in [('tex-1', tex), ('bibtex', [tools['bibtex'], 'pair_baseline']),
                          ('tex-2', tex), ('tex-3', tex)]:
        execute(manifest, out, name, command, build / 'proofs')
    log = (build / 'proofs/pair_baseline.log').read_text(errors='replace')
    blg = (build / 'proofs/pair_baseline.blg').read_text(errors='replace')
    failures, warnings = tex_diagnostics(log)
    warnings.extend(line for line in blg.splitlines() if 'Warning' in line)
    if 'Warning--I didn\'t find a database entry' in blg:
        failures.append('BibTeX could not find a cited database entry')
    manifest['pdf'] = {'status': 'fail' if failures else 'pass',
                       'failures': failures, 'warnings': warnings}
    if failures:
        raise RuntimeError('unresolved TeX references/citations or rerun request; see build/proofs/pair_baseline.log')
    pdf = build / 'proofs/pair_baseline.pdf'
    if not pdf.is_file() or not pdf.read_bytes().startswith(b'%PDF-'):
        raise RuntimeError('TeX did not produce a PDF')
    shutil.copy2(pdf, out / 'pair_baseline.pdf')
    pages = re.search(r'Output written on .*?\((\d+) pages?', log, re.S)
    manifest['pdf']['pages'] = int(pages[1]) if pages else None


def reproduce(root, out, checks_only=False):
    manifest = {
        'schema_version': 1, 'task': 'verification_and_exposition',
        'assumptions': ['UNCONDITIONAL'], 'analytic_proof_certificate': False,
        'claim_ids': ['PAIR-ASYMPTOTIC-001'], 'claim_status': 'proved-draft',
        'mode': 'checks-only' if checks_only else 'full', 'status': 'running',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'source': {'root': str(root), 'commit': None, 'dirty': None},
        'environment': {'python': sys.version, 'python_executable': sys.executable,
                        'platform': platform.platform(), 'provisioned_by_harness': False},
        'inputs': {}, 'stages': [], 'tests': {'status': 'not_run'},
        'pdf': {'status': 'skipped' if checks_only else 'not_run'},
        'external_computational_proofs_replayed': False,
    }
    try:
        manifest['inputs'] = input_hashes(root)
        tools = collect_environment(root, out, manifest, checks_only)
        run_checks(root, out, manifest)
        print('Regenerating normalization and error records...', flush=True)
        report = generate()
        validate_sources(report, root)
        (out / 'pair-normalization.json').write_text(json_text(report), encoding='utf-8')
        (out / 'pair-normalization.md').write_text(markdown(report), encoding='utf-8')
        manifest['stages'].append({'name': 'normalization', 'status': 'pass',
                                   'operation': 'exact monomial normalization and substitution'})
        if not checks_only:
            build_pdf(root, out, manifest, tools)
        if input_hashes(root) != manifest['inputs']:
            raise RuntimeError('source inputs changed during reproduction')
        manifest['status'] = 'partial' if checks_only else 'pass'
    except (OSError, ValueError, RuntimeError) as error:
        manifest.update(status='fail', error=str(error))
    finally:
        manifest['finished_utc'] = datetime.now(timezone.utc).isoformat()
        manifest['outputs'] = {
            str(p.relative_to(out)): sha256(p) for p in sorted(out.rglob('*'))
            if p.is_file() and p.name != 'manifest.json'}
        (out / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n',
                                          encoding='utf-8')
    print(f"Reproduction {manifest['status']}: {out}", flush=True)
    if manifest['status'] == 'fail':
        print(manifest['error'], file=sys.stderr)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checks-only', action='store_true',
                        help='run checks and regenerate formulas, explicitly skipping the PDF')
    parser.add_argument('--output-dir', type=Path,
                        help='new/empty destination; inside the repo use artifacts/reproduction/')
    args = parser.parse_args()
    try:
        out = prepare_output(ROOT, args.output_dir)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    manifest = reproduce(ROOT, out, args.checks_only)
    return 1 if manifest['status'] == 'fail' else 0


if __name__ == '__main__':
    sys.exit(main())
