#!/usr/bin/env python3
"""Reproduce the Lean milestones; archive actual successes or failures.

This command can download dependencies. No theorem status is edited by the runner.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import shlex
import signal
import subprocess
import sys
import time

from bootstrap_lean import ROOT, TOOLS, PINS, environment, upstream_checkout


def digest(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def source_hashes():
    files = [ROOT / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
             'research/lean-import-pins.json', 'scripts/bootstrap_lean.py',
             'scripts/reproduce_lean.py', 'scripts/check_lean_reproduction.py', 'scripts/check_triple_expansion.py', 'research/lean-verification.md', 'scripts/check_zeta23_import.py', 'research/lean-zeta23-inventory.json', 'research/lean-zeta23.md', 'research/lean-pair-zero-inventory.json', 'research/lean-pair-zero.md', 'research/lean-pair-zero-bounds-inventory.json', 'research/lean-pair-zero-bounds.md', 'research/lean-pair-zero-comparison-inventory.json', 'research/lean-pair-zero-comparison.md', 'research/lean-pair-asymptotic-inventory.json', 'research/lean-pair-asymptotic.md', 'research/lean-pair-fourier-inventory.json', 'research/lean-pair-fourier.md', 'research/lean-triple-master-inventory.json', 'research/lean-triple-master.md', 'scripts/prepare_lean_diagonal.py', 'scripts/check_lean_analytic_coverage.py',
             'research/lean-analytic-coverage.json', 'research/lean-actual-occurrences-inventory.json',
             'research/lean-rational-transfer-inventory.json', 'research/lean-integral-profile-inventory.json', 'research/lean-uniform-height-inventory.json', 'research/lean-pair-series-inventory.json', 'research/lean-paired-mellin-inventory.json', 'research/lean-pair-exact-inventory.json', 'research/lean-pair-uniform-inventory.json', 'research/lean-pair-meanvalue-inventory.json', 'research/lean-pair-sieve-inventory.json', 'research/lean-pair-diagonal-inventory.json', 'research/lean-pair-prime-mean-inventory.json', 'research/lean-pair-rhs-mean-inventory.json']]
    files += sorted(p for p in (ROOT / 'vendor/zeta23').rglob('*') if p.is_file())
    files += sorted((ROOT / 'lean').rglob('*.lean'))
    files += sorted((ROOT / 'lean').rglob('*.json'))
    return {str(p.relative_to(ROOT)): digest(p) for p in files if p.is_file()}


def verify_upstream_checkout():
    """Read-only counterpart of bootstrap's clone-if-missing operation."""
    checkout = ROOT / '.lake/packages/OAI'
    if not (checkout / '.git').exists():
        raise RuntimeError('Missing OAI checkout; run without --reuse-dependencies to prepare it')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    if head != PINS['upstream']['rev']:
        raise RuntimeError('OAI checkout disagrees with the pinned revision')
    if subprocess.check_output(['git', 'diff', 'HEAD', '--'], cwd=checkout):
        raise RuntimeError('OAI tracked source differs from the pinned commit')


def verify_dependency_pins():
    verify_upstream_checkout()
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    upstream_manifest = json.loads(subprocess.check_output(
        ['git', 'show', PINS['upstream']['rev'] + ':lean/lake-manifest.json'],
        cwd=ROOT / '.lake/packages/OAI', text=True))
    expected_pins = {p['name']: p['rev'] for p in upstream_manifest['packages']}
    actual_pins = {p['name']: p['rev'] for p in manifest['packages'] if p['type'] == 'git'}
    if actual_pins != expected_pins:
        raise RuntimeError('Resolved dependency pins differ from upstream locked manifest')
    for name, expected in [('mathlib', PINS['upstream']['mathlib_rev'])]:
        if packages[name]['rev'] != expected:
            raise RuntimeError(f'{name}: resolved revision does not match pin')
    for name, p in packages.items():
        if p['type'] == 'git':
            checkout = ROOT / manifest['packagesDir'] / name.strip('«»')
            if not (checkout / '.git').exists():
                raise RuntimeError(f'{name}: missing dependency checkout at {checkout}; run without --reuse-dependencies to prepare it')
            actual = subprocess.check_output(
                ['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
            if actual != p['rev']:
                raise RuntimeError(f'{name}: checkout disagrees with lockfile')


def verify_prepared_dependencies():
    """Check preparation without fetching, patching, or changing any checkout."""
    from prepare_lean_diagonal import REPLACEMENTS

    verify_dependency_pins()
    upstream = ROOT / '.lake/packages/OAI'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {p['name'].strip('«»'): ROOT / manifest['packagesDir'] / p['name'].strip('«»')
                for p in manifest['packages'] if p['type'] == 'git'}
    # Enumerate from the pinned Git tree so a missing patch cannot silently disappear.
    paths = subprocess.check_output(
        ['git', 'ls-tree', '-r', '--name-only', PINS['upstream']['rev'], '--', 'lean/patches'],
        cwd=upstream, text=True).splitlines()
    patches = [p for p in paths if p.endswith('.patch')]
    if not patches:
        raise RuntimeError('Pinned upstream has no compatibility patches')
    checked = {}
    for relative in patches:
        patch = upstream / relative
        suffix = '-lean4341.patch'
        if not patch.name.endswith(suffix) or patch.name[:-len(suffix)] not in packages:
            raise RuntimeError(f'Unrecognized pinned compatibility patch: {relative}')
        name = patch.name[:-len(suffix)]
        result = subprocess.run(['git', 'apply', '--check', '--reverse', str(patch)],
                                cwd=packages[name], capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(f'{name}: required compatibility patch is missing or conflicts; '
                               f'run without --reuse-dependencies to prepare it.\n{result.stderr}')
        checked[name] = digest(patch)
    target = packages['PrimeNumberTheoremAnd'] / 'PrimeNumberTheoremAnd/MediumPNT.lean'
    if not target.is_file() or any(target.read_text().count(new) != 1 for _, new in REPLACEMENTS):
        raise RuntimeError('PNT smoothing adapter is not prepared; run scripts/prepare_lean_diagonal.py')
    for relative in ['elan/bin/elan', 'elan/bin/lean', 'elan/bin/lake', 'go/bin/go',
                     'bin/landrun', 'comparator/.lake/build/bin/comparator',
                     'comparator/.lake/packages/lean4export/.lake/build/bin/lean4export']:
        path = TOOLS / relative
        if not path.is_file() or not os.access(path, os.X_OK):
            raise RuntimeError(f'Missing executable {path}; run scripts/bootstrap_lean.py')
    # `elan which` checks installation without auto-installing the selected toolchain.
    result = subprocess.run([str(TOOLS / 'elan/bin/elan'), 'which', 'lean'],
                            env=environment(), capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'Pinned Lean toolchain is unavailable; run scripts/bootstrap_lean.py\n{result.stderr}')
    return dict(status='pass', patches=checked, pnt_adapter_sha256=digest(target),
                lean_executable=result.stdout.strip())


def run_command(run_dir, report, name, argv, *, expected_failure=False):
    """Log each stage and preserve its outcome even when interrupted."""
    argv = list(map(str, argv))
    log = run_dir / (name + '.log')
    entry = dict(name=name, argv=argv, exit_code=None, log=log.name,
                 expected_failure=expected_failure, status='running')
    report['commands'].append(entry)
    print(f'{name}: {shlex.join(argv)}\n  Log: {log}\n  Follow progress: tail -f {shlex.quote(str(log))}', flush=True)
    started = time.monotonic()
    try:
        with log.open('w') as out:
            process = subprocess.Popen(argv, cwd=ROOT, env=environment(), stdout=out,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                entry['exit_code'] = process.wait()
            except KeyboardInterrupt:
                # Stop the stage's descendants too (Lake may have spawned Git/curl/Lean).
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                entry['exit_code'] = process.returncode
                raise
        text = log.read_text(errors='replace')
        if expected_failure:
            if entry['exit_code'] == 0 or "Illegal axiom detected: 'sorryAx'" not in text:
                raise RuntimeError(f'{name}: did not reject the unfinished proof for sorryAx')
        elif entry['exit_code']:
            raise RuntimeError(f'{name}: exit {entry["exit_code"]}; see {log}')
        entry['status'] = 'pass'
        return text
    except KeyboardInterrupt:
        entry['status'] = 'interrupted'
        raise
    except Exception as exc:
        entry.update(status='fail', error=str(exc))
        raise
    finally:
        entry['duration_seconds'] = round(time.monotonic() - started, 3)
        print(f'{name}: {entry["status"]} ({entry["duration_seconds"]:.1f}s)', flush=True)


def dependency_evidence(run_dir):
    """Preserve actual compatibility changes, not just their upstream recipe."""
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    records = {}
    for p in manifest['packages']:
        if p['type'] != 'git':
            continue
        name = p['name'].strip('«»')
        checkout = ROOT / manifest['packagesDir'] / name
        diff = subprocess.check_output(['git', 'diff', '--binary', 'HEAD', '--'], cwd=checkout)
        filename = 'dependency-' + name + '.diff'
        (run_dir / filename).write_bytes(diff)
        records[name] = dict(rev=p['rev'], tracked_diff=filename,
                            tracked_diff_sha256=hashlib.sha256(diff).hexdigest())
    return records


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-bootstrap', action='store_true')
    parser.add_argument('--reuse-dependencies', action='store_true',
                        help='Verify existing dependencies and tools; skip bootstrap, resolution, PNT preparation and cache downloads. All selected proof checks still run.')
    parser.add_argument('--fresh-project', action='store_true',
                        help='Move aside only the project build directory before verification.')
    parser.add_argument('--zeta23-only', action='store_true',
                        help='Use prepared dependencies; check Zeta23, combined build, all axioms and regressions.')
    parser.add_argument('--pair-zero-only', action='store_true',
                        help='Use prepared dependencies; check the exact zero-side decomposition, combined build, all axioms and regressions.')
    parser.add_argument('--pair-zero-bounds-only', action='store_true',
                        help='Use prepared dependencies; check uniform zero-side errors, combined build, all axioms and regressions.')
    parser.add_argument('--pair-zero-comparison-only', action='store_true',
                        help='Use prepared dependencies; check optimized cutoff and uniform pair comparison, combined build, all axioms and regressions.')
    parser.add_argument('--pair-asymptotic-only', action='store_true',
                        help='Use prepared dependencies; check the normalized pair asymptotic, combined build, all axioms and regressions.')
    parser.add_argument('--pair-fourier-only', action='store_true',
                        help='Use prepared dependencies; check pair Fourier translation and test limits, combined build, all axioms and regressions.')
    parser.add_argument('--triple-master-only', action='store_true',
                        help='Use prepared dependencies; check the triple integral-norm bound, interchange, kernel identity, five subseries, 27-word expansion cubic prime Fourier identity and exact resonance split, combined build, all axioms and regressions.')
    args = parser.parse_args(argv)
    if sum([args.pair_zero_only, args.zeta23_only, args.pair_zero_bounds_only, args.pair_zero_comparison_only, args.pair_asymptotic_only, args.pair_fourier_only, args.triple_master_only]) > 1:
        parser.error('Choose at most one focused verification mode')
    prepared = args.reuse_dependencies or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run_dir = ROOT / 'artifacts/lean-runs' / stamp
    run_dir.mkdir(parents=True)
    report = dict(schema_version=1, task='formal_verification', started_utc=stamp,
                  status='running', pins=PINS, commands=[], external_kernel=False,
                  fresh_project_build=args.fresh_project, source_hashes=source_hashes(),
                  dependency_mode='reuse' if prepared else 'prepare',
                  bootstrap_skipped=args.skip_bootstrap or args.reuse_dependencies,
                  assumptions=['UNCONDITIONAL'],
                  verification_scope='Zeta import, strip corollaries, finite foundation, horizontal-square bounds, analytic summability foundations, actual zero-occurrence convergence, rational-kernel transfer, integral-profile identification, horizontal derivatives, logarithmic local zero counts, uniform height bounds, pair explicit-formula series convergence, the paired Mellin kernel including its endpoint, the exact pair explicit formula, its uniform named errors, the Fourier mean-value input with actual prime-series specialization, the effective weighted nearby-prime sieve bound, the prime diagonal asymptotic, the optimized prime mean square, the complete explicit-formula RHS mean square with existential constants, the Zeta23 imports, the exact zero-side decomposition, uniform zero-side error bounds, and the optimized uniform pair comparison using QRH-STRIP-001, the normalized pair asymptotic with existential constants, the exact pair Fourier translation and test-function limit, and the triple master integral-norm bound, interchange, exact kernel identity, five subseries and ordered 27-word expansion')

    if args.zeta23_only:
        report['verification_scope'] = ('Zeta23 rank-trace and dyadic counting imports; combined project build, '
            'complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.pair_zero_only:
        report['verification_scope'] = ('Exact pair zero-side decomposition and finite norm identity; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.pair_zero_bounds_only:
        report['verification_scope'] = ('Uniform pair zero-side error bounds and finite horizontal envelope; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.pair_zero_comparison_only:
        report['verification_scope'] = ('Optimized cutoff and uniform pair comparison using the pinned PREPRINT strip theorem; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.pair_asymptotic_only:
        report['verification_scope'] = ('Normalized pair asymptotic, finite symmetry, normalized error budget and endpoints using the pinned PREPRINT comparison; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.pair_fourier_only:
        report['verification_scope'] = ('Exact pair Fourier translation and the test-function asymptotic and limit; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_master_only:
        report['verification_scope'] = ('Triple master integral-norm bound, sum-integral interchange, exact kernel identity, five subseries, independent cutoff limits and ordered 27-word expansion; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    def command(name, argv, *, expected_failure=False):
        return run_command(run_dir, report, name, argv, expected_failure=expected_failure)

    try:
        if prepared:
            print('dependency-preflight: checking existing pins, patches, PNT preparation and tools', flush=True)
            report['dependency_preflight'] = verify_prepared_dependencies()
            print('dependency-preflight: pass; dependency setup and cache downloads skipped', flush=True)
        if not (args.skip_bootstrap or args.reuse_dependencies):
            command('bootstrap', [sys.executable, '-B', 'scripts/bootstrap_lean.py'])
        command('lean-version', ['lean', '--version'])
        command('python-version', [sys.executable, '--version'])
        command('git-version', ['git', '--version'])
        command('go-version', ['go', 'version'])
        command('landrun-version', ['landrun', '--version'])
        if not prepared:
            upstream_checkout()
        # Runs upstream's required patch hooks; check every resolved Git pin afterward.
        if not prepared:
            command('resolve', ['lake', 'update', 'OAI'])
            command('prepare-diagonal', [sys.executable, '-B', 'scripts/prepare_lean_diagonal.py'])
        verify_dependency_pins()
        report['dependency_checkouts'] = dependency_evidence(run_dir)
        if not prepared:
            command('mathlib-cache', ['lake', 'exe', 'cache', 'get'])
        if args.fresh_project:
            build = ROOT / '.lake/build'
            if build.exists():
                build.rename(ROOT / '.lake' / ('previous-build-' + stamp))
        comparator = TOOLS / 'comparator/.lake/build/bin/comparator'
        upstream = ROOT / '.lake/packages/OAI/lean'
        if not (args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only):
            command('triple-master-build', ['lake', 'build', 'HigherCorrelations.TriplePrimeResonance'])
            command('triple-master-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master.json'])
            command('triple-master-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-unfinished.json'], expected_failure=True)
            command('triple-master-identity-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-identity-unfinished.json'], expected_failure=True)
            command('triple-master-patterns-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-patterns-unfinished.json'], expected_failure=True)
            command('triple-master-expansion-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-expansion-unfinished.json'], expected_failure=True)
            command('triple-master-prime-fourier-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-prime-fourier-unfinished.json'], expected_failure=True)
            command('triple-master-resonance-classification-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-resonance-classification-unfinished.json'], expected_failure=True)
            command('triple-master-resonance-split-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-resonance-split-unfinished.json'], expected_failure=True)
        if not (args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.triple_master_only):
            command('pair-fourier-build', ['lake', 'build', 'HigherCorrelations.PairFourierAsymptotic'])
            command('pair-fourier-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-fourier.json'])
            command('pair-fourier-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-fourier-unfinished.json'], expected_failure=True)
        if not (args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-asymptotic-build', ['lake', 'build', 'HigherCorrelations.PairAsymptotic'])
            command('pair-asymptotic-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-asymptotic.json'])
            command('pair-asymptotic-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-asymptotic-unfinished.json'], expected_failure=True)
        if not (args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-zero-comparison-build', ['lake', 'build', 'HigherCorrelations.PairZeroComparison'])
            command('pair-zero-comparison-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-comparison.json'])
            command('pair-zero-comparison-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-comparison-unfinished.json'], expected_failure=True)
        if not (args.zeta23_only or args.pair_zero_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-zero-bounds-build', ['lake', 'build', 'HigherCorrelations.PairZeroUniformBounds'])
            command('pair-zero-bounds-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-bounds.json'])
            command('pair-zero-bounds-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-bounds-unfinished.json'], expected_failure=True)
        if not (args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-zero-build', ['lake', 'build', 'HigherCorrelations.PairZeroDecomposition'])
            command('pair-zero-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero.json'])
            command('pair-zero-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-unfinished.json'], expected_failure=True)
        if not (args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('zeta23-provenance', [sys.executable, '-B', 'scripts/check_zeta23_import.py'])
            command('zeta23-build', ['lake', 'build', 'HigherCorrelations.Zeta23RankTrace',
                                    'HigherCorrelations.Zeta23Counting'])
            for suite in ['zeta23-ranktrace', 'zeta23-counting']:
                command(suite + '-comparator', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/' + suite + '.json'])
            command('zeta23-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/zeta23-unfinished.json'], expected_failure=True)
        command('project-build', ['lake', 'build', 'HigherCorrelations'])
        command('analytic-coverage', [sys.executable, '-B', 'scripts/check_lean_analytic_coverage.py'])
        if not (args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-rhs-mean-build', ['lake', 'build', 'HigherCorrelations.PairRHSMean'])
            command('pair-rhs-mean-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-rhs-mean.json'])
            command('pair-rhs-mean-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-rhs-mean-unfinished.json'], expected_failure=True)
            command('pair-prime-mean-build', ['lake', 'build', 'HigherCorrelations.PairPrimeMean'])
            command('pair-prime-mean-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-prime-mean.json'])
            command('pair-prime-mean-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-prime-mean-unfinished.json'], expected_failure=True)
            command('pair-diagonal-build', ['lake', 'build', 'HigherCorrelations.PairDiagonalEndpoints'])
            command('pair-diagonal-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-diagonal.json'])
            command('pair-diagonal-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-diagonal-unfinished.json'], expected_failure=True)
            command('pair-sieve-build', ['lake', 'build', 'HigherCorrelations.PairSieveEndpoints'])
            command('pair-sieve-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-sieve.json'])
            command('pair-sieve-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-sieve-unfinished.json'], expected_failure=True)
            command('pair-meanvalue-build', ['lake', 'build', 'HigherCorrelations.PairMeanEndpoints'])
            command('pair-meanvalue-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-meanvalue.json'])
            command('pair-meanvalue-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-meanvalue-unfinished.json'], expected_failure=True)
            command('pair-uniform-build', ['lake', 'build', 'HigherCorrelations.PairUniformFormula'])
            command('pair-uniform-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-uniform.json'])
            command('pair-uniform-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-uniform-unfinished.json'], expected_failure=True)
            command('pair-exact-build', ['lake', 'build', 'HigherCorrelations.PairExactFormula'])
            command('pair-exact-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-exact.json'])
            command('pair-exact-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-exact-unfinished.json'], expected_failure=True)
            command('paired-mellin-build', ['lake', 'build', 'HigherCorrelations.PairedMellin'])
            command('paired-mellin-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/paired-mellin.json'])
            command('paired-mellin-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/paired-mellin-unfinished.json'], expected_failure=True)
            command('pair-series-build', ['lake', 'build', 'HigherCorrelations.PairSeriesConvergence'])
            command('pair-series-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-series.json'])
            command('pair-series-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-series-unfinished.json'], expected_failure=True)
            command('uniform-height-build', ['lake', 'build', 'HigherCorrelations.UniformHeight'])
            command('uniform-height-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/uniform-height.json'])
            command('uniform-height-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/uniform-height-unfinished.json'], expected_failure=True)
            command('integral-profile-build', ['lake', 'build', 'HigherCorrelations.IntegralProfile'])
            command('integral-profile-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/integral-profile.json'])
            command('integral-profile-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/integral-profile-unfinished.json'], expected_failure=True)
            command('rational-transfer-build', ['lake', 'build', 'HigherCorrelations.RationalTransfer'])
            command('rational-transfer-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/rational-transfer.json'])
            command('rational-transfer-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/rational-transfer-unfinished.json'], expected_failure=True)
            command('actual-occurrences-build', ['lake', 'build', 'HigherCorrelations.ActualOccurrencesFoundation'])
            command('actual-occurrences-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/actual-occurrences.json'])
            command('actual-occurrences-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/actual-occurrences-unfinished.json'], expected_failure=True)
            command('summability-build', ['lake', 'build', 'HigherCorrelations.SummabilityFoundation'])
            command('summability-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/summability.json'])
            command('summability-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/summability-unfinished.json'], expected_failure=True)
            command('horizontal-square-build', ['lake', 'build', 'HigherCorrelations.HorizontalSquareFoundation'])
            command('horizontal-square-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/horizontal-square.json'])
            command('horizontal-square-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/horizontal-square-unfinished.json'], expected_failure=True)
            command('finite-build', ['lake', 'build', 'HigherCorrelations.FiniteFoundation'])
            command('finite-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/finite-foundation.json'])
            command('finite-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/finite-unfinished.json'], expected_failure=True)
            command('upstream-comparator', ['lake', 'env', comparator,
                    upstream / 'ComparatorChallenges/QuasiRiemannHypothesis.json'])
            command('project-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/horizontal-strip.json'])
            command('unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/unfinished.json'], expected_failure=True)
        axioms = command('axioms', ['lake', 'env', 'lean',
                                   'lean/HigherCorrelations/AxiomReport.lean'])
        entries = re.findall(r"'(\S+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", axioms)
        allowed = {'propext', 'Quot.sound', 'Classical.choice'}
        expected = set(json.loads((ROOT / 'lean/VerificationChallenges/horizontal-strip.json').read_text())['theorem_names'])
        expected.update(json.loads((ROOT / 'lean/VerificationChallenges/finite-foundation.json').read_text())['theorem_names'])
        expected.update(json.loads((ROOT / 'lean/VerificationChallenges/horizontal-square.json').read_text())['theorem_names'])
        expected.update(json.loads((ROOT / 'lean/VerificationChallenges/summability.json').read_text())['theorem_names'])
        actual_inventory = json.loads((ROOT / 'research/lean-actual-occurrences-inventory.json').read_text())
        expected.update(c['declaration'] for c in actual_inventory['components'])
        expected.update(actual_inventory['imported_axioms'])
        rational_inventory = json.loads((ROOT / 'research/lean-rational-transfer-inventory.json').read_text())
        expected.update(c['declaration'] for c in rational_inventory['components'])
        profile_inventory = json.loads((ROOT / 'research/lean-integral-profile-inventory.json').read_text())
        expected.update(c['declaration'] for c in profile_inventory['components'])
        expected.update(profile_inventory['imported_axioms'])
        uniform_inventory = json.loads((ROOT / 'research/lean-uniform-height-inventory.json').read_text())
        expected.update(c['declaration'] for c in uniform_inventory['components'])
        expected.update(uniform_inventory['imported_axioms'])
        pair_inventory = json.loads((ROOT / 'research/lean-pair-series-inventory.json').read_text())
        expected.update(c['declaration'] for c in pair_inventory['components'])
        expected.update(pair_inventory['imported_axioms'])
        mellin_inventory = json.loads((ROOT / 'research/lean-paired-mellin-inventory.json').read_text())
        expected.update(c['declaration'] for c in mellin_inventory['components'])
        expected.update(mellin_inventory['imported_axioms'])
        exact_inventory = json.loads((ROOT / 'research/lean-pair-exact-inventory.json').read_text())
        expected.update(c['declaration'] for c in exact_inventory['components'])
        expected.update(exact_inventory['imported_axioms'])
        pair_uniform_inventory = json.loads((ROOT / 'research/lean-pair-uniform-inventory.json').read_text())
        expected.update(c['declaration'] for c in pair_uniform_inventory['components'])
        expected.update(pair_uniform_inventory['imported_axioms'])
        mean_inventory = json.loads((ROOT / 'research/lean-pair-meanvalue-inventory.json').read_text())
        expected.update(c['declaration'] for c in mean_inventory['components'])
        expected.update(mean_inventory['imported_axioms'])
        sieve_inventory = json.loads((ROOT / 'research/lean-pair-sieve-inventory.json').read_text())
        expected.update(c['declaration'] for c in sieve_inventory['components'])
        expected.update(sieve_inventory['imported_axioms'])
        diagonal_inventory = json.loads((ROOT / 'research/lean-pair-diagonal-inventory.json').read_text())
        expected.update(c['declaration'] for c in diagonal_inventory['components'])
        expected.update(diagonal_inventory['imported_axioms'])
        prime_mean_inventory = json.loads((ROOT / 'research/lean-pair-prime-mean-inventory.json').read_text())
        expected.update(c['declaration'] for c in prime_mean_inventory['components'])
        expected.update(prime_mean_inventory['imported_axioms'])
        rhs_mean_inventory = json.loads((ROOT / 'research/lean-pair-rhs-mean-inventory.json').read_text())
        expected.update(c['declaration'] for c in rhs_mean_inventory['components'])
        expected.update(rhs_mean_inventory['imported_axioms'])
        zeta23_inventory = json.loads((ROOT / 'research/lean-zeta23-inventory.json').read_text())
        expected.update(c['declaration'] for c in zeta23_inventory['components'])
        expected.update(zeta23_inventory['imported_axioms'])
        zero_inventory = json.loads((ROOT / 'research/lean-pair-zero-inventory.json').read_text())
        expected.update(c['declaration'] for c in zero_inventory['components'])
        expected.update(zero_inventory['imported_axioms'])
        bounds_inventory = json.loads((ROOT / 'research/lean-pair-zero-bounds-inventory.json').read_text())
        expected.update(c['declaration'] for c in bounds_inventory['components'])
        expected.update(bounds_inventory['imported_axioms'])
        comparison_inventory = json.loads((ROOT / 'research/lean-pair-zero-comparison-inventory.json').read_text())
        expected.update(c['declaration'] for c in comparison_inventory['components'])
        expected.update(comparison_inventory['imported_axioms'])
        asymptotic_inventory = json.loads((ROOT / 'research/lean-pair-asymptotic-inventory.json').read_text())
        expected.update(c['declaration'] for c in asymptotic_inventory['components'])
        expected.update(asymptotic_inventory['imported_axioms'])
        fourier_inventory = json.loads((ROOT / 'research/lean-pair-fourier-inventory.json').read_text())
        expected.update(c['declaration'] for c in fourier_inventory['components'])
        expected.update(fourier_inventory['imported_axioms'])
        master_inventory = json.loads((ROOT / 'research/lean-triple-master-inventory.json').read_text())
        expected.update(c['declaration'] for c in master_inventory['components'])
        expected.update(master_inventory['imported_axioms'])
        expected.add('OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re')
        if (len(entries) != len(expected) or {name for name, _ in entries} != expected
                or any(set(re.findall(r'[\w.]+', e)) - allowed for _, e in entries)):
            raise RuntimeError('Axiom report incomplete or contains unexpected axioms')
        command('pair-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                    '-s', 'scripts', '-p', 'check_pair_*.py'])
        command('triple-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                      '-s', 'scripts', '-p', 'check_triple_*.py'])
        command('harness-regressions', [sys.executable, '-B', 'scripts/check_lean_reproduction.py'])
        report['status'] = 'pass'
    except KeyboardInterrupt:
        report['status'] = 'interrupted'
        report['error'] = 'Interrupted by user; verification did not complete'
        print(report['error'], file=sys.stderr, flush=True)
    except Exception as exc:
        report['status'] = 'fail'
        report['error'] = str(exc)
        print(str(exc), file=sys.stderr, flush=True)
    finally:
        report['source_hashes'] = source_hashes()
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        report['source_commit'] = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        report['worktree_dirty'] = bool(subprocess.check_output(
            ['git', 'status', '--porcelain'], cwd=ROOT, text=True))
        report['outputs'] = {p.name: digest(p) for p in sorted(run_dir.iterdir()) if p.is_file()}
        patches = ROOT / '.lake/packages/OAI/lean/patches'
        report['upstream_patch_hashes'] = {p.name: digest(p) for p in sorted(patches.glob('*.patch'))}
        report['tool_binary_hashes'] = {str(p.relative_to(ROOT)): digest(p) for p in [
            TOOLS / 'bin/landrun', TOOLS / 'comparator/.lake/build/bin/comparator',
            TOOLS / 'comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'] if p.is_file()}
        raw = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
        (run_dir / 'manifest.json').write_bytes(raw)
        target = ROOT / 'artifacts/certificates/lean' / hashlib.sha256(raw).hexdigest()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(run_dir, target)
        print('Report:', target / 'manifest.json', flush=True)
    return 130 if report['status'] == 'interrupted' else 0 if report['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
