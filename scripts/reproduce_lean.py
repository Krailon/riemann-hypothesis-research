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
from lean_control_pool import available_cpus, cancel_queued, control_entry, run_control_pool, utc_now


def digest(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def source_hashes():
    files = [ROOT / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
             'research/lean-import-pins.json', 'scripts/bootstrap_lean.py',
             'scripts/check_lean_littlewood.py', 'research/lean-littlewood-inventory.json', 'research/lean-littlewood.md', 'scripts/check_lean_density_adapters.py', 'research/lean-density-adapters-inventory.json', 'research/lean-density-adapters.md', 'scripts/check_lean_constant_kernel.py', 'research/lean-constant-kernel-inventory.json', 'research/lean-constant-kernel.md', 'scripts/reproduce_lean.py', 'scripts/lean_control_pool.py', 'scripts/check_lean_control_pool.py', 'scripts/check_lean_reproduction.py', 'scripts/check_triple_expansion.py', 'scripts/check_lean_triple_smoothed_correlation.py', 'research/lean-triple-smoothed-correlation-inventory.json', 'research/lean-triple-smoothed-correlation.md', 'scripts/check_lean_triple_main_term_comparison.py', 'research/lean-triple-main-term-comparison-inventory.json', 'research/lean-triple-main-term-comparison.md', 'research/lean-verification.md', 'scripts/check_lean_triple_sine_measure.py', 'research/lean-triple-sine-measure-inventory.json', 'research/lean-triple-sine-measure.md', 'scripts/check_zeta23_import.py', 'research/lean-zeta23-inventory.json', 'research/lean-zeta23.md', 'research/lean-pair-zero-inventory.json', 'research/lean-pair-zero.md', 'research/lean-pair-zero-bounds-inventory.json', 'research/lean-pair-zero-bounds.md', 'research/lean-pair-zero-comparison-inventory.json', 'research/lean-pair-zero-comparison.md', 'research/lean-pair-asymptotic-inventory.json', 'research/lean-pair-asymptotic.md', 'research/lean-pair-fourier-inventory.json', 'research/lean-pair-fourier.md', 'research/lean-triple-master-inventory.json', 'research/lean-triple-master.md', 'research/lean-triple-budget-inventory.json', 'research/lean-triple-budget.md', 'scripts/check_lean_triple_budget.py', 'research/lean-triple-mixed-diagonal-inventory.json', 'research/lean-triple-mixed-diagonal.md', 'scripts/check_lean_triple_mixed_diagonal.py', 'research/lean-triple-smoothing-inventory.json', 'research/lean-triple-smoothing.md', 'scripts/check_lean_triple_smoothing.py', 'research/lean-triple-resonance-decay-inventory.json', 'research/lean-triple-resonance-decay.md', 'scripts/check_lean_triple_resonance_decay.py', 'research/lean-triple-retained-inventory.json', 'research/lean-triple-retained.md', 'scripts/check_lean_triple_retained.py', 'research/lean-triple-interior-vanishing-inventory.json', 'research/lean-triple-interior-vanishing.md', 'scripts/check_lean_triple_interior_vanishing.py', 'research/lean-triple-test-function-inventory.json', 'research/lean-triple-test-function.md', 'scripts/check_lean_triple_test_function.py', 'research/lean-triple-boundary-inventory.json', 'research/lean-triple-boundary.md', 'scripts/check_lean_triple_boundary.py', 'research/lean-triple-signed-sectors-inventory.json', 'research/lean-triple-signed-sectors.md', 'scripts/check_lean_triple_signed_sectors.py', 'research/lean-triple-kernel-localization-inventory.json', 'research/lean-triple-kernel-localization.md', 'scripts/check_lean_triple_kernel_localization.py', 'scripts/prepare_lean_diagonal.py', 'scripts/check_lean_analytic_coverage.py',
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
                 expected_failure=expected_failure, status='running', started_utc=utc_now())
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
        entry['finished_utc'] = utc_now()
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
                        help='Use prepared dependencies; check the triple integral-norm bound, interchange, kernel identity, five subseries, 27-word expansion cubic prime Fourier identity exact resonance split, Fourier decay and assembled master theorem, combined build, all axioms and regressions.')
    parser.add_argument('--triple-budget-only', action='store_true',
                        help='Use prepared dependencies; check the uniform triple budget and additive limit, combined build, all axioms and regressions.')
    parser.add_argument('--triple-mixed-diagonal-only', action='store_true',
                        help='Check the uniform mixed-prime diagonal, combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-smoothing-only', action='store_true',
                        help='Check the sharper first smoothing moment, combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-resonance-decay-only', action='store_true',
                        help='Check the decaying resonance bound, combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-retained-only', action='store_true',
                        help='Check the assembled retained-term evaluation, combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-interior-vanishing-only', action='store_true',
                        help='Check uniform interior bounds and limits, combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-test-function-only', action='store_true',
                        help='Check the interior weighted test-function passage, combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-boundary-only', action='store_true',
                        help='Check quadrant axes, origin, local uniform profiles and full-zero limit; combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-signed-sectors-only', action='store_true',
                        help='Check signed sectors, full smooth-test passage and limit; combined build, all axioms and regressions using prepared dependencies.')
    parser.add_argument('--triple-kernel-localization-only', action='store_true',
                        help='Check kernel localization, summed near/far bounds and complex-test weighted frozen-profile summability, normalized transfer, height limits, uniform microscopic profile and tuplewise critical-line quadratic expansion, and explicit zero-gap horizontal profile and local normalization; combined build, axioms and regressions using prepared dependencies.')
    parser.add_argument('--littlewood-only', action='store_true',
                        help='Verify Littlewood boundary logarithms, exact identity and multiplicity-preserving zeta count bounds.')
    parser.add_argument('--density-adapters-only', action='store_true',
                        help='Verify finite density counts and explicitly conditional reflection/window transfers.')
    parser.add_argument('--constant-kernel-only', action='store_true',
                        help='Verify pointwise, project-scaled and summed constant-kernel replacement, quadratic Fourier decay and cutoffs.')
    parser.add_argument('--triple-smoothed-correlation-only', action='store_true',
                        help='Verify the unit-normalized smoothed triple theorem and varying families.')
    parser.add_argument('--triple-main-term-comparison-only', action='store_true',
                        help='Check exact and weighted sine benchmark comparison with inherited error bounds and limits.')
    parser.add_argument('--triple-sine-measure-only', action='store_true',
                        help='Check the full sine benchmark, five partition Fourier rows and cumulants; combined build, axioms and regressions using prepared dependencies.')
    parser.add_argument('--control-jobs', type=int, default=4, metavar='N',
                        help='Parallel rejection controls (default 4, capped by CPU affinity); 1 preserves serial ordering.')
    args = parser.parse_args(argv)
    if args.control_jobs < 1:
        parser.error('--control-jobs must be a positive integer')
    cpu_count = available_cpus()
    control_jobs = min(args.control_jobs, cpu_count)
    if sum([args.littlewood_only, args.density_adapters_only, args.constant_kernel_only, args.triple_smoothed_correlation_only, args.triple_main_term_comparison_only, args.pair_zero_only, args.zeta23_only, args.pair_zero_bounds_only, args.pair_zero_comparison_only, args.pair_asymptotic_only, args.pair_fourier_only, args.triple_master_only, args.triple_budget_only, args.triple_mixed_diagonal_only, args.triple_smoothing_only, args.triple_resonance_decay_only, args.triple_retained_only, args.triple_interior_vanishing_only, args.triple_test_function_only, args.triple_boundary_only, args.triple_signed_sectors_only, args.triple_kernel_localization_only, args.triple_sine_measure_only]) > 1:
        parser.error('Choose at most one focused verification mode')
    prepared = args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.reuse_dependencies or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only or args.triple_signed_sectors_only or args.triple_kernel_localization_only or args.triple_sine_measure_only
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run_dir = ROOT / 'artifacts/lean-runs' / stamp
    run_dir.mkdir(parents=True)
    report = dict(schema_version=2, task='formal_verification', started_utc=stamp,
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

    if args.triple_budget_only:
        report['verification_scope'] = ('Uniform triple named budget, logarithmic-gap lemma, grouped off-diagonal bounds and additive asymptotic; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_mixed_diagonal_only:
        report['verification_scope'] = ('Uniform two-scale mixed-prime diagonal, finite Abel identity and inclusive endpoints; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_smoothing_only:
        report['verification_scope'] = ('Sharp first smoothing moment, exact correction integral, explicit bounds and fixed-weight limit; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_resonance_decay_only:
        report['verification_scope'] = ('Square-root proper-power count, absolutely summable dyadic cover, explicit resonance decay and endpoints; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_retained_only:
        report['verification_scope'] = ('Exact retained-term evaluation, named errors, combined additive bound, symmetry and endpoints; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_interior_vanishing_only:
        report['verification_scope'] = ('Uniform retained and full-observable interior bounds, moving-range limits and inclusive endpoints; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_test_function_only:
        report['verification_scope'] = ('Interior weighted test-function passage: support margins, entire/Schwartz inversion, absolute frequency interchange, local-spacing bound and limit; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_boundary_only:
        report['verification_scope'] = ('Quadrant Fourier passage, integrated boundary budget, origin and both axis uniform profiles, normalized asymptotic and full-zero identity; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_signed_sectors_only:
        report['verification_scope'] = ('Signed positive-base convergence, six-sector geometry and conjugation, sharp hexagonal majorant, full complex-test identity and uniform asymptotic; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun.')

    if args.triple_kernel_localization_only:
        report['verification_scope'] = ('Exact anchored profile translation, tuplewise localization, the disjoint near/far budgets, summed error bound, signed complex-test majorant and absolute unweighted/weighted frozen-profile convergence with uniform mass bounds, independent fixed-height cutoffs, normalized correlation transfer, fixed-test height limits effective microscopic profile convergence, the explicit critical-line quadratic expansion and tuplewise specialization, the real zero-gap horizontal profile with closed-cube denominator positivity, and local normalization with coefficient limit 3/2; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun. No ordinate-only replacement or varying-parameter limit is asserted. Summed constants remain absolute existential constants.')

    if args.triple_sine_measure_only:
        report['verification_scope'] = ('Full sine benchmark: overlap geometry, cycle transform, Schwartz pairings, continuous marginals and line restrictions, all five Fourier rows, tempered realization, ordinary and factorial cumulants, and closed-hexagon cancellation; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun. No main-term comparison or zeta support-boundary extension is asserted.')

    if args.triple_main_term_comparison_only:
        report['verification_scope'] = ('Exact inverse-transform benchmark comparison, support cancellation, native and frozen weighted bounds and normalized limits; '
            'combined project build, complete axiom report and Python regressions. Earlier Comparator suites are not rerun. '
            'Constants retain their inherited existential status. No ordinate-only replacement or zeta support-boundary extension is asserted.')

    if args.triple_smoothed_correlation_only:
        report['verification_scope'] = ('Unit-normalized smoothed triple theorem: exact profile sum, absolute convergence, independent cutoffs, separate and combined uniform errors, supremum specialization, fixed and varying-family limits; '
            'combined project build, complete axiom report and regressions. Earlier Comparator suites are not rerun. Uniform constants remain existential; no ordinate-only or closed support-boundary conclusion.')

    if args.constant_kernel_only:
        report['verification_scope'] = ('Pointwise eight-reflection bound with explicit constant 4096pi, project-scaled kernel bound, uniform quadratic P24 Fourier decay, fixed-height summability, normalized moment bound, splitting and cutoffs; '
            'combined build, complete axiom audit and regressions. No density-based vanishing or kernel-free signed-error limit.')

    if args.density_adapters_only:
        report['verification_scope'] = ('Finite multiplicity-preserving density counts, endpoint identities, reflection, dyadic covers, and conditional comparable-window and scaled-tail estimates; '
            'combined build, complete axiom audit and regressions. UniformDyadicDensity remains an explicit hypothesis; no density theorem or signed-error limit is proved.')

    if args.littlewood_only:
        report['verification_scope'] = ('Littlewood transported boundary logarithms, integrability, exact weighted identity, finite product orders, additive multiplicity counts and actual mollified-zeta adapters on zero-free rectangle boundaries; '
            'combined build, complete axiom audit and regressions. No analytic density theorem or boundary-zero limiting extension.')

    controls = []
    deferred_build = []
    report['rejection_controls'] = dict(requested_jobs=args.control_jobs, cpu_affinity_count=cpu_count,
                                       effective_jobs=control_jobs,
                                       mode='parallel' if control_jobs > 1 else 'serial')

    def command(name, argv, *, expected_failure=False):
        if control_jobs > 1 and expected_failure:
            entry = control_entry(name, argv)
            controls.append(entry)
            # Keep deterministic declaration order, irrespective of execution order.
            report['commands'].append(entry)
            return ''
        if control_jobs > 1 and name == 'project-build':
            deferred_build.append((name, argv))
            return ''
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
        if not (args.constant_kernel_only or args.density_adapters_only or args.pair_asymptotic_only or args.pair_fourier_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_zero_only or args.triple_boundary_only or args.triple_budget_only or args.triple_interior_vanishing_only or args.triple_kernel_localization_only or args.triple_main_term_comparison_only or args.triple_master_only or args.triple_mixed_diagonal_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_signed_sectors_only or args.triple_sine_measure_only or args.triple_smoothed_correlation_only or args.triple_smoothing_only or args.triple_test_function_only or args.zeta23_only):
            if not args.littlewood_only:
                report['verification_scope'] += '; Littlewood identity and zero-free-boundary horizontal count adapters'
            command('littlewood-build', ['lake', 'build', 'HigherCorrelations.LittlewoodProductExamples'])
            command('littlewood-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/littlewood.json'])
            from check_lean_littlewood import CONTROLS as littlewood_controls
            for control in littlewood_controls:
                command('littlewood-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/littlewood-' + control + '-unfinished.json'], expected_failure=True)
            command('littlewood-regressions', [sys.executable, '-B', 'scripts/check_lean_littlewood.py'])
        if not (args.littlewood_only or args.constant_kernel_only or args.pair_asymptotic_only or args.pair_fourier_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_zero_only or args.triple_boundary_only or args.triple_budget_only or args.triple_interior_vanishing_only or args.triple_kernel_localization_only or args.triple_main_term_comparison_only or args.triple_master_only or args.triple_mixed_diagonal_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_signed_sectors_only or args.triple_sine_measure_only or args.triple_smoothed_correlation_only or args.triple_smoothing_only or args.triple_test_function_only or args.zeta23_only):
            report['conditional_hypotheses'] = ['UniformDyadicDensity C T₀; no proved instance']
            report['assumptions'].append('ZERO_DENSITY(C>0, T₀>=3, for all V>=T₀ and 0<=D<=331/1000: # {occurrences: V<gamma<=2V, beta-1/2>D} <= C*(V^(1-D/4)*log V+(log V)^2))')
            if not args.density_adapters_only:
                report['verification_scope'] += '; finite density adapters and explicitly conditional uniform window/tail implications'
            command('density-adapters-build', ['lake', 'build', 'HigherCorrelations.DensityWindowAdapters'])
            command('density-adapters-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/density-adapters.json'])
            from check_lean_density_adapters import CONTROLS as density_controls
            for control in density_controls:
                command('density-adapters-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/density-adapters-' + control + '-unfinished.json'], expected_failure=True)
            command('density-adapters-regressions', [sys.executable, '-B', 'scripts/check_lean_density_adapters.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only or args.triple_signed_sectors_only or args.triple_kernel_localization_only or args.triple_sine_measure_only):
            command('constant-kernel-build', ['lake', 'build', 'HigherCorrelations.ReplacementAssembly'])
            command('constant-kernel-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/constant-kernel.json'])
            for control in ['profile', 'horizontal', 'gap', 'pointwise', 'origin', 'coincident', 'endpoints', 'scaled', 'fourier-convention', 'quadratic-decay', 'tuple-decay', 'moment-summability', 'summability', 'split', 'summed', 'cutoff', 'normalization']:
                command('constant-kernel-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/constant-kernel-' + control + '-unfinished.json'], expected_failure=True)
            command('constant-kernel-regressions', [sys.executable, '-B', 'scripts/check_lean_constant_kernel.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only or args.triple_signed_sectors_only or args.triple_kernel_localization_only):
            command('triple-smoothed-correlation-build', ['lake', 'build', 'HigherCorrelations.SmoothedTripleTheorem'])
            command('triple-smoothed-correlation-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-smoothed-correlation.json'])
            for control in ['normalization', 'summability', 'cutoff', 'height-cutoff', 'profile', 'uniform', 'supremum', 'fixed-limit', 'varying-limit']:
                command('triple-smoothed-correlation-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-smoothed-correlation-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-smoothed-correlation-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_smoothed_correlation.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_sine_measure_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only or args.triple_signed_sectors_only or args.triple_kernel_localization_only):
            command('triple-main-term-comparison-build', ['lake', 'build', 'HigherCorrelations.MainTermComparisonAssembly'])
            command('triple-main-term-comparison-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-main-term-comparison.json'])
            for control in ['adapter', 'reflection', 'support', 'comparison', 'signed-bound', 'frozen-bound', 'signed-limit', 'frozen-limit']:
                command('triple-main-term-comparison-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-main-term-comparison-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-main-term-comparison-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_main_term_comparison.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only or args.triple_signed_sectors_only or args.triple_kernel_localization_only):
            command('triple-sine-measure-build', ['lake', 'build', 'HigherCorrelations.SineMeasureAssembly'])
            command('triple-sine-measure-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-sine-measure.json'])
            for control in ['span', 'volume', 'integrability', 'integral', 'endpoint', 'sectors', 'parameter', 'transform', 'weighted', 'pairing', 'squared', 'mass', 'marginal', 'slice', 'line-duality', 'five-rows', 'benchmark', 'tempered', 'ordinary', 'factorial', 'closed', 'covariance']:
                command('triple-sine-measure-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-sine-measure-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-sine-measure-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_sine_measure.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only or args.triple_signed_sectors_only):
            command('triple-kernel-localization-build', ['lake', 'build', 'HigherCorrelations.TripleKernelLocalizationAssembly'])
            command('triple-kernel-localization-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-kernel-localization.json'])
            for control in ['translation', 'decomposition', 'sharp', 'bound', 'regions', 'near', 'far-center', 'far-anchor', 'summability', 'frozen-summability', 'frozen-normalization', 'frozen-cutoff', 'complex-test', 'weighted-profile', 'weighted-error', 'weighted-cutoff', 'profile-normalization', 'profile-transfer', 'profile-limit', 'micro-gap', 'micro-rate', 'micro-limit', 'critical-expansion', 'critical-rate', 'critical-quadratic-tuple', 'critical-leading-tuple', 'horizontal-denominator', 'horizontal-formula', 'horizontal-target', 'local-normalization', 'local-coefficient-limit', 'local-endpoint']:
                command('triple-kernel-localization-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-kernel-localization-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-kernel-localization-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_kernel_localization.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only or args.triple_test_function_only or args.triple_boundary_only):
            command('triple-signed-sectors-build', ['lake', 'build', 'HigherCorrelations.TripleSignedAssembly'])
            command('triple-signed-sectors-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-signed-sectors.json'])
            for control in ['reflection', 'interchange', 'support', 'conjugation', 'normalization', 'limit']:
                command('triple-signed-sectors-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-signed-sectors-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-signed-sectors-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_signed_sectors.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_test_function_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only):
            command('triple-boundary-build', ['lake', 'build', 'HigherCorrelations.TripleBoundaryAssembly'])
            command('triple-boundary-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-boundary.json'])
            for control in ['interchange', 'budget', 'origin', 'axis', 'limit', 'distribution']:
                command('triple-boundary-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-boundary-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-boundary-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_boundary.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only or args.triple_interior_vanishing_only):
            command('triple-test-function-build', ['lake', 'build', 'HigherCorrelations.TripleTestAssembly'])
            command('triple-test-function-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-test-function.json'])
            for control in ['regularity', 'interchange', 'bound', 'limit']:
                command('triple-test-function-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-test-function-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-test-function-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_test_function.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.pair_zero_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only or args.triple_retained_only):
            command('triple-interior-vanishing-build', ['lake', 'build', 'HigherCorrelations.TripleInteriorVanishing'])
            command('triple-interior-vanishing-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-interior-vanishing.json'])
            for control in ['retained', 'observable', 'limit']:
                command('triple-interior-vanishing-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-interior-vanishing-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-interior-vanishing-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_interior_vanishing.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only or args.triple_resonance_decay_only):
            command('triple-retained-build', ['lake', 'build', 'HigherCorrelations.TripleRetainedEndpoints'])
            command('triple-retained-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-retained.json'])
            for control in ['identity', 'diagonal', 'evaluation']:
                command('triple-retained-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-retained-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-retained-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_retained.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only or args.triple_smoothing_only):
            command('triple-resonance-decay-build', ['lake', 'build', 'HigherCorrelations.TripleResonanceEndpoints'])
            command('triple-resonance-decay-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-resonance-decay.json'])
            for control in ['count', 'summability', 'decay']:
                command('triple-resonance-decay-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-resonance-decay-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-resonance-decay-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_resonance_decay.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only or args.triple_mixed_diagonal_only):
            command('triple-smoothing-build', ['lake', 'build', 'HigherCorrelations.TripleSmoothingMoment'])
            command('triple-smoothing-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-smoothing.json'])
            for control in ['identity', 'sharp']:
                command('triple-smoothing-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-smoothing-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-smoothing-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_smoothing.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only or args.triple_budget_only):
            command('triple-mixed-diagonal-build', ['lake', 'build', 'HigherCorrelations.TripleMixedDiagonalEndpoints'])
            command('triple-mixed-diagonal-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-mixed-diagonal.json'])
            for control in ['finite', 'asymptotic', 'endpoints']:
                command('triple-mixed-diagonal-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-mixed-diagonal-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-mixed-diagonal-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_mixed_diagonal.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('triple-budget-build', ['lake', 'build', 'HigherCorrelations.TripleBudgetAssembly'])
            command('triple-budget-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-budget.json'])
            for control in ['accounting', 'refinement', 'gap', 'offdiag', 'asymptotic', 'limit']:
                command('triple-budget-' + control + '-unfinished-rejected', ['lake', 'env', comparator,
                        'lean/VerificationChallenges/triple-budget-' + control + '-unfinished.json'], expected_failure=True)
            command('triple-budget-regressions', [sys.executable, '-B', 'scripts/check_lean_triple_budget.py'])
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only):
            command('triple-master-build', ['lake', 'build', 'HigherCorrelations.TripleMasterAssembly'])
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
            command('triple-master-fourier-decay-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-fourier-decay-unfinished.json'], expected_failure=True)
            command('triple-master-cubic-decay-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-cubic-decay-unfinished.json'], expected_failure=True)
            command('triple-master-assembly-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-assembly-unfinished.json'], expected_failure=True)
            command('triple-master-uniform-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/triple-master-uniform-unfinished.json'], expected_failure=True)
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.triple_master_only):
            command('pair-fourier-build', ['lake', 'build', 'HigherCorrelations.PairFourierAsymptotic'])
            command('pair-fourier-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-fourier.json'])
            command('pair-fourier-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-fourier-unfinished.json'], expected_failure=True)
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-asymptotic-build', ['lake', 'build', 'HigherCorrelations.PairAsymptotic'])
            command('pair-asymptotic-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-asymptotic.json'])
            command('pair-asymptotic-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-asymptotic-unfinished.json'], expected_failure=True)
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-zero-comparison-build', ['lake', 'build', 'HigherCorrelations.PairZeroComparison'])
            command('pair-zero-comparison-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-comparison.json'])
            command('pair-zero-comparison-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-comparison-unfinished.json'], expected_failure=True)
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-zero-bounds-build', ['lake', 'build', 'HigherCorrelations.PairZeroUniformBounds'])
            command('pair-zero-bounds-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-bounds.json'])
            command('pair-zero-bounds-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-bounds-unfinished.json'], expected_failure=True)
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
            command('pair-zero-build', ['lake', 'build', 'HigherCorrelations.PairZeroDecomposition'])
            command('pair-zero-comparator', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero.json'])
            command('pair-zero-unfinished-rejected', ['lake', 'env', comparator,
                    'lean/VerificationChallenges/pair-zero-unfinished.json'], expected_failure=True)
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
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
        if not (args.littlewood_only or args.density_adapters_only or args.constant_kernel_only or args.triple_smoothed_correlation_only or args.triple_main_term_comparison_only or args.triple_sine_measure_only or args.triple_kernel_localization_only or args.triple_signed_sectors_only or args.triple_boundary_only or args.triple_test_function_only or args.triple_interior_vanishing_only or args.triple_retained_only or args.triple_resonance_decay_only or args.triple_smoothing_only or args.triple_mixed_diagonal_only or args.triple_budget_only or args.zeta23_only or args.pair_zero_only or args.pair_zero_bounds_only or args.pair_zero_comparison_only or args.pair_asymptotic_only or args.pair_fourier_only or args.triple_master_only):
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
        if controls:
            modules = set()
            for entry in controls:
                config = json.loads((ROOT / entry['argv'][-1]).read_text())
                modules.update([config['challenge_module'], config['solution_module']])
            command('rejection-controls-prebuild', ['lake', 'build', *sorted(modules)])
            run_control_pool(ROOT, run_dir, controls, control_jobs, environment(), report['rejection_controls'])
        for name, argv in deferred_build:
            run_command(run_dir, report, name, argv)
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
        budget_inventory = json.loads((ROOT / 'research/lean-triple-budget-inventory.json').read_text())
        expected.update(c['declaration'] for c in budget_inventory['components'])
        expected.update(budget_inventory['imported_axioms'])
        mixed_inventory = json.loads((ROOT / 'research/lean-triple-mixed-diagonal-inventory.json').read_text())
        expected.update(c['declaration'] for c in mixed_inventory['components'])
        expected.update(mixed_inventory['imported_axioms'])
        smoothing_inventory = json.loads((ROOT / 'research/lean-triple-smoothing-inventory.json').read_text())
        expected.update(c['declaration'] for c in smoothing_inventory['components'])
        expected.update(smoothing_inventory['imported_axioms'])
        resonance_inventory = json.loads((ROOT / 'research/lean-triple-resonance-decay-inventory.json').read_text())
        expected.update(c['declaration'] for c in resonance_inventory['components'])
        expected.update(resonance_inventory['imported_axioms'])
        retained_inventory = json.loads((ROOT / 'research/lean-triple-retained-inventory.json').read_text())
        expected.update(c['declaration'] for c in retained_inventory['components'])
        expected.update(retained_inventory['imported_axioms'])
        interior_inventory = json.loads((ROOT / 'research/lean-triple-interior-vanishing-inventory.json').read_text())
        expected.update(c['declaration'] for c in interior_inventory['components'])
        expected.update(interior_inventory['imported_axioms'])
        test_function_inventory = json.loads((ROOT / 'research/lean-triple-test-function-inventory.json').read_text())
        expected.update(c['declaration'] for c in test_function_inventory['components'])
        expected.update(test_function_inventory['imported_axioms'])
        boundary_inventory = json.loads((ROOT / 'research/lean-triple-boundary-inventory.json').read_text())
        expected.update(c['declaration'] for c in boundary_inventory['components'])
        expected.update(boundary_inventory['imported_axioms'])
        signed_inventory = json.loads((ROOT / 'research/lean-triple-signed-sectors-inventory.json').read_text())
        expected.update(c['declaration'] for c in signed_inventory['components'])
        expected.update(signed_inventory['imported_axioms'])
        localization_inventory = json.loads((ROOT / 'research/lean-triple-kernel-localization-inventory.json').read_text())
        expected.update(c['declaration'] for c in localization_inventory['components'])
        expected.update(localization_inventory['imported_axioms'])
        sine_inventory = json.loads((ROOT / 'research/lean-triple-sine-measure-inventory.json').read_text())
        expected.update(c['declaration'] for c in sine_inventory['components'])
        comparison_inventory = json.loads((ROOT / 'research/lean-triple-main-term-comparison-inventory.json').read_text())
        expected.update(c['declaration'] for c in comparison_inventory['components'])
        smoothed_inventory = json.loads((ROOT / 'research/lean-triple-smoothed-correlation-inventory.json').read_text())
        expected.update(c['declaration'] for c in smoothed_inventory['components'])
        constant_inventory = json.loads((ROOT / 'research/lean-constant-kernel-inventory.json').read_text())
        expected.update(c['declaration'] for c in constant_inventory['components'])
        density_inventory = json.loads((ROOT / 'research/lean-density-adapters-inventory.json').read_text())
        expected.update(c['declaration'] for c in density_inventory['components'])
        littlewood_inventory = json.loads((ROOT / 'research/lean-littlewood-inventory.json').read_text())
        expected.update(c['declaration'] for c in littlewood_inventory['components'])
        expected.update(littlewood_inventory['imported_axioms'])
        expected.add('OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re')
        if (len(entries) != len(expected) or {name for name, _ in entries} != expected
                or any(set(re.findall(r'[\w.]+', e)) - allowed for _, e in entries)):
            raise RuntimeError('Axiom report incomplete or contains unexpected axioms')
        command('pair-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                    '-s', 'scripts', '-p', 'check_pair_*.py'])
        command('triple-regressions', [sys.executable, '-B', '-m', 'unittest', 'discover',
                                      '-s', 'scripts', '-p', 'check_triple_*.py'])
        command('harness-regressions', [sys.executable, '-B', 'scripts/check_lean_reproduction.py'])
        command('control-pool-regressions', [sys.executable, '-B', 'scripts/check_lean_control_pool.py'])
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
        cancel_queued(controls)
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
