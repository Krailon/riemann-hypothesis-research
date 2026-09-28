"""Harness regressions. Task: verification. Assumptions: UNCONDITIONAL.

Tests exercise finite exact algebra and orchestration; no analytic certificate.
Nested workflow tests mock suite execution to avoid recursive discovery.
"""

from contextlib import redirect_stderr, redirect_stdout
from copy import deepcopy
from fractions import Fraction as Q
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from pair_normalization import Monomial, generate, json_text, markdown, validate_sources
import reproduce_pair as runner


def evaluate(term, values, sqrt_q):
    result = Q(term['coefficient'])
    for name, power in term['powers'].items():
        exponent = Q(power)
        if name == 'q':
            base, exponent = sqrt_q, 2*exponent
        else:
            base = values[name]
        if exponent.denominator != 1:
            raise AssertionError('fixture does not give a rational power')
        result *= base**int(exponent)
    return result


class PairReproduction(unittest.TestCase):
    def test_generated_main_and_each_error_against_independent_values(self):
        report = generate()
        # Same kind of exact fixtures as check_pair_asymptotic, independently
        # evaluating the exported powers rather than trusting display strings.
        for t, x, s, log_x in [(Q(3), Q(1), Q(11, 10), Q(0)),
                               (Q(16), Q(4), Q(2), Q(2)),
                               (Q(81), Q(81), Q(3), Q(9))]:
            q = s*s
            values = {'T': t, 'X': x, 'l': log_x}
            expected = [q/x**2, log_x/q, 1/x**2, 1/s, 1/q, x/(t*q)]
            for row, want in zip(report['rows'], expected, strict=True):
                got = evaluate(row['after_normalization'], values, s)
                before = evaluate(row['before_normalization'], values, s)
                self.assertEqual(got, want)
                self.assertEqual(got, before/(t*q))

    def test_substitution_and_all_three_endpoints(self):
        report = generate()
        for n in range(5):
            a, t, x, s = Q(n, 4), Q(81), Q(3**n), Q(3)
            values = {'T': t, 'X': x, 'l': a*s*s, 'a': a, 'v': x}
            for row in report['rows']:
                self.assertEqual(evaluate(row['after_normalization'], values, s),
                                 evaluate(row['after_substitution'], values, s))
        for point in report['endpoints']:
            a = abs(Q(point['alpha']))
            values = {'T': Q(81)}
            main = [evaluate(term, values, Q(3)) for term in point['main_terms']]
            errors = [evaluate(term, values, Q(3)) for term in point['absolute_error_scales']]
            self.assertEqual(main, [Q(9)*Q(81)**(-2*int(a)), a])
            self.assertEqual(errors, [Q(81)**(-2*int(a)), Q(1, 3)])
        self.assertEqual(report['endpoints'][0]['absolute_error_scales'][0]['expression'], '1')

    def test_comparison_signs_and_absorption_ratios(self):
        r = generate()
        for key, sign in r['comparison_signs']['L_minus_2piPhi'].items():
            self.assertEqual(r['comparison_signs']['2piPhi_minus_L'][key], -sign)
        for t, x, s in [(Q(3), Q(1), Q(11, 10)), (Q(81), Q(81), Q(3))]:
            values = {'T': t, 'X': x}
            self.assertEqual(evaluate(r['absorption']['comparison_X_over_comparison_T'], values, s), x/t)
            self.assertEqual(evaluate(r['absorption']['comparison_T_over_mean'], values, s), 1/s)
        # Generic division really computes exponents and coefficients.
        self.assertEqual(Monomial.make(6, T=2).divide(Monomial.make(3, T=1)),
                         Monomial.make(2, T=1))

    def test_deterministic_artifacts_and_source_locators(self):
        first, second = generate(), generate()
        self.assertEqual(json_text(first), json_text(second))
        self.assertEqual(markdown(first), markdown(second))
        self.assertEqual(json.loads(json_text(first)), first)
        validate_sources(first, runner.ROOT)
        bad = deepcopy(first)
        bad['rows'][0]['source']['label'] = 'missing-label'
        with self.assertRaisesRegex(ValueError, 'missing manuscript label'):
            validate_sources(bad, runner.ROOT)

    def test_output_collision_and_source_directory_protection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / 'repo'
            root.mkdir()
            existing = root / 'artifacts/reproduction/used'
            existing.mkdir(parents=True)
            (existing / 'keep.txt').write_text('keep')
            with self.assertRaises(ValueError):
                runner.prepare_output(root, existing)
            self.assertEqual((existing / 'keep.txt').read_text(), 'keep')
            with self.assertRaises(ValueError):
                runner.prepare_output(root, root / 'research/new')
            empty = Path(tmp) / 'empty'
            empty.mkdir()
            self.assertEqual(runner.prepare_output(root, empty), empty)
            self.assertNotEqual(runner.prepare_output(root, None), runner.prepare_output(root, None))

    def test_failed_subprocess_retains_log_and_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            manifest = {'stages': []}
            with self.assertRaisesRegex(RuntimeError, 'failed'):
                runner.execute(manifest, out, 'deliberate-failure',
                               [sys.executable, '-c', 'print("diagnostic"); raise SystemExit(7)'], out)
            self.assertIn('diagnostic', (out / 'logs/deliberate-failure.log').read_text())
            self.assertEqual(manifest['stages'][0]['returncode'], 7)
            self.assertEqual(manifest['stages'][0]['status'], 'fail')

    def test_missing_tool_and_python_version_diagnostics(self):
        with patch.object(runner.shutil, 'which', return_value=None):
            with self.assertRaisesRegex(RuntimeError, 'missing prerequisite: git'):
                runner.collect_environment(runner.ROOT, runner.ROOT, {'environment': {}}, True)
        with patch.object(runner.sys, 'version_info', (3, 11)):
            with self.assertRaisesRegex(RuntimeError, 'Python 3.12'):
                runner.collect_environment(runner.ROOT, runner.ROOT, {}, True)
        with patch.object(runner.shutil, 'which', side_effect=lambda name: '/git' if name == 'git' else None), \
                patch.object(runner, 'execute', return_value=''):
            with self.assertRaisesRegex(RuntimeError, 'missing prerequisite: pdflatex'):
                runner.collect_environment(runner.ROOT, runner.ROOT, {'environment': {}, 'source': {}}, False)

    def test_suite_summary_rejects_empty_failed_or_skipped_discovery(self):
        self.assertEqual(runner.check_test_log('Ran 70 tests in 1s\n\nOK\n'), 70)
        for text in ['Ran 0 tests in 0s\nOK\n', 'Ran 59 tests in 1s\nFAILED\n',
                     'Ran 60 tests in 1s\nOK (skipped=1)\n', 'OK\n']:
            with self.assertRaises(RuntimeError):
                runner.check_test_log(text)

    def test_final_tex_diagnostics(self):
        for warning in ["LaTeX Warning: Reference `x' undefined.",
                        'LaTeX Warning: There were undefined citations.',
                        'LaTeX Warning: Label(s) may have changed. Rerun.',
                        'Package rerunfilecheck Warning: Rerun to get outlines right',
                        '(rerunfilecheck) Rerun to get outlines right',
                        'LaTeX Warning: There were multiply defined labels.']:
            self.assertTrue(runner.tex_diagnostics(warning)[0])
        failures, warnings = runner.tex_diagnostics('Overfull box\nPackage foo Warning: layout\n')
        self.assertFalse(failures)
        self.assertEqual(len(warnings), 2)
        self.assertEqual(runner.tex_diagnostics(
            '(/tex/rerunfilecheck/rerunfilecheck.sty\n'
            'Package: rerunfilecheck v1.10 Rerun checks for auxiliary files\n'
            'Package rerunfilecheck Info: File has not changed.\n'
            '(rerunfilecheck) Checksum: 123;456.\n'), ([], []))

    def test_partial_run_and_failure_manifests(self):
        # No nested test suite: orchestrate with stubbed suite and environment.
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(runner, 'collect_environment', return_value={}), \
                patch.object(runner, 'run_checks'), \
                patch.object(runner, 'build_pdf') as build, \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            out = Path(tmp)
            result = runner.reproduce(runner.ROOT, out, checks_only=True)
            self.assertEqual(result['status'], 'partial')
            self.assertEqual(result['pdf']['status'], 'skipped')
            build.assert_not_called()
            recorded = json.loads((out / 'manifest.json').read_text())
            for path, expected_hash in recorded['outputs'].items():
                self.assertEqual(runner.sha256(out / path), expected_hash)
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(runner, 'collect_environment', side_effect=RuntimeError('missing tool')), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            result = runner.reproduce(runner.ROOT, Path(tmp))
            self.assertEqual(result['status'], 'fail')
            self.assertEqual(result['error'], 'missing tool')
            self.assertTrue((Path(tmp) / 'manifest.json').exists())

    def test_failed_audit_stops_artifact_generation(self):
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(runner, 'collect_environment', return_value={}), \
                patch.object(runner, 'run_checks', side_effect=RuntimeError('stale source hash')), \
                patch.object(runner, 'generate') as generator, \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            result = runner.reproduce(runner.ROOT, Path(tmp))
            self.assertEqual(result['status'], 'fail')
            generator.assert_not_called()
            self.assertFalse((Path(tmp) / 'pair-normalization.json').exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
