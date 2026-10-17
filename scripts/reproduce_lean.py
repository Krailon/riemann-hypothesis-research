#!/usr/bin/env python3
"""Reproduce the Lean milestones; archive actual successes or failures.

This command can download dependencies. No theorem status is edited by the runner.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

from bootstrap_lean import ROOT, TOOLS, PINS, environment, upstream_checkout


def digest(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def source_hashes():
    files = [ROOT / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
             'research/lean-import-pins.json', 'scripts/bootstrap_lean.py',
             'scripts/reproduce_lean.py', 'scripts/prepare_lean_diagonal.py', 'scripts/check_lean_analytic_coverage.py',
             'research/lean-analytic-coverage.json', 'research/lean-actual-occurrences-inventory.json',
             'research/lean-rational-transfer-inventory.json', 'research/lean-integral-profile-inventory.json', 'research/lean-uniform-height-inventory.json', 'research/lean-pair-series-inventory.json', 'research/lean-paired-mellin-inventory.json', 'research/lean-pair-exact-inventory.json', 'research/lean-pair-uniform-inventory.json', 'research/lean-pair-meanvalue-inventory.json', 'research/lean-pair-sieve-inventory.json', 'research/lean-pair-diagonal-inventory.json']]
    files += sorted((ROOT / 'lean').rglob('*.lean'))
    files += sorted((ROOT / 'lean').rglob('*.json'))
    return {str(p.relative_to(ROOT)): digest(p) for p in files if p.is_file()}


def verify_dependency_pins():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    upstream_checkout()
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
            actual = subprocess.check_output(
                ['git', 'rev-parse', 'HEAD'],
                cwd=ROOT / manifest['packagesDir'] / name.strip('«»'),
                text=True).strip()
            if actual != p['rev']:
                raise RuntimeError(f'{name}: checkout disagrees with lockfile')


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-bootstrap', action='store_true')
    parser.add_argument('--fresh-project', action='store_true',
                        help='Move aside only the project build directory before verification.')
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run_dir = ROOT / 'artifacts/lean-runs' / stamp
    run_dir.mkdir(parents=True)
    report = dict(schema_version=1, task='formal_verification', started_utc=stamp,
                  status='running', pins=PINS, commands=[], external_kernel=False,
                  fresh_project_build=args.fresh_project, source_hashes=source_hashes(),
                  assumptions=['UNCONDITIONAL'],
                  verification_scope='Zeta import, strip corollaries, finite foundation, horizontal-square bounds, analytic summability foundations, actual zero-occurrence convergence, rational-kernel transfer, integral-profile identification, horizontal derivatives, logarithmic local zero counts, uniform height bounds, pair explicit-formula series convergence, the paired Mellin kernel including its endpoint, the exact pair explicit formula, its uniform named errors, the Fourier mean-value input with actual prime-series specialization, the effective weighted nearby-prime sieve bound, and the prime diagonal asymptotic with existential constants')

    def command(name, argv, *, expected_failure=False):
        log = run_dir / (name + '.log')
        print(f'{name}: {log}', flush=True)
        with log.open('w') as out:
            process = subprocess.run(list(map(str, argv)), cwd=ROOT, env=environment(),
                                     stdout=out, stderr=subprocess.STDOUT)
        report['commands'].append(dict(name=name, argv=list(map(str, argv)),
                                      exit_code=process.returncode, log=log.name,
                                      expected_failure=expected_failure))
        text = log.read_text(errors='replace')
        if expected_failure:
            if process.returncode == 0 or "Illegal axiom detected: 'sorryAx'" not in text:
                raise RuntimeError(f'{name}: did not reject the unfinished proof for sorryAx')
        elif process.returncode:
            raise RuntimeError(f'{name}: exit {process.returncode}; see {log}')
        print(f'{name}: pass', flush=True)
        return text

    try:
        if not args.skip_bootstrap:
            command('bootstrap', [sys.executable, '-B', 'scripts/bootstrap_lean.py'])
        command('lean-version', ['lean', '--version'])
        command('python-version', [sys.executable, '--version'])
        command('git-version', ['git', '--version'])
        command('go-version', ['go', 'version'])
        command('landrun-version', ['landrun', '--version'])
        upstream_checkout()
        # Runs upstream's required patch hooks; check every resolved Git pin afterward.
        command('resolve', ['lake', 'update', 'OAI'])
        command('prepare-diagonal', [sys.executable, '-B', 'scripts/prepare_lean_diagonal.py'])
        verify_dependency_pins()
        report['dependency_checkouts'] = dependency_evidence(run_dir)
        command('mathlib-cache', ['lake', 'exe', 'cache', 'get'])
        if args.fresh_project:
            build = ROOT / '.lake/build'
            if build.exists():
                build.rename(ROOT / '.lake' / ('previous-build-' + stamp))
        comparator = TOOLS / 'comparator/.lake/build/bin/comparator'
        upstream = ROOT / '.lake/packages/OAI/lean'
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
        command('analytic-coverage', [sys.executable, '-B', 'scripts/check_lean_analytic_coverage.py'])
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
        command('project-build', ['lake', 'build', 'HigherCorrelations'])
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
        expected.add('OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re')
        if (len(entries) != len(expected) or {name for name, _ in entries} != expected
                or any(set(re.findall(r'[\w.]+', e)) - allowed for _, e in entries)):
            raise RuntimeError('Axiom report incomplete or contains unexpected axioms')
        command('pair-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                    '-s', 'scripts', '-p', 'check_pair_*.py'])
        command('triple-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                      '-s', 'scripts', '-p', 'check_triple_*.py'])
        report['status'] = 'pass'
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
    return 0 if report['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
