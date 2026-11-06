#!/usr/bin/env python3
"""UNCONDITIONAL harness regression tests; no mathematical proof certification.

Proof-suite execution is mocked in orchestration tests. Dependency preflight and
process logging are exercised separately, without downloads or proof rebuilds.
"""
from contextlib import ExitStack, redirect_stdout, redirect_stderr
import io
import json
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import reproduce_lean as runner
from prepare_lean_diagonal import REPLACEMENTS

REAL_ROOT = runner.ROOT


class LeanReproductionTests(unittest.TestCase):
    def run_workflow(self, flags, *, interrupt=False, preflight_error=None, jobs=1, pool_error=None):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            root = Path(tmp)
            for name in ['lean', 'research']:
                (root / name).symlink_to(REAL_ROOT / name, target_is_directory=True)
            names = re.findall(r'^#print axioms (\S+)',
                               (REAL_ROOT / 'lean/HigherCorrelations/AxiomReport.lean').read_text(), re.M)
            calls = []

            def command(run_dir, report, name, argv, *, expected_failure=False):
                calls.append(name)
                log = run_dir / (name + '.log')
                log.write_text('test fixture\n')
                report['commands'].append(dict(name=name, status='pass', exit_code=0, log=log.name))
                if interrupt:
                    report['commands'][-1].update(status='interrupted', exit_code=-signal.SIGTERM)
                    raise KeyboardInterrupt
                if name == 'axioms':
                    return '\n'.join(f"'{n}' depends on axioms: [propext, Quot.sound, Classical.choice]" for n in names)
                return ''

            def pool(root, run_dir, entries, jobs, env, metadata):
                metadata['effective_jobs'] = min(jobs, len(entries))
                if pool_error:
                    raise pool_error
                for entry in entries:
                    calls.append(entry['name'])
                    entry.update(status='pass', exit_code=1)
                    (run_dir / entry['log']).write_text("Illegal axiom detected: 'sorryAx'\n")

            stack.enter_context(patch.object(runner, 'run_control_pool', side_effect=pool))
            stack.enter_context(patch.object(runner, 'available_cpus', return_value=32))
            stack.enter_context(patch.object(runner, 'ROOT', root))
            stack.enter_context(patch.object(runner, 'TOOLS', root / '.tools'))
            stack.enter_context(patch.object(runner, 'run_command', side_effect=command))
            stack.enter_context(patch.object(runner, 'source_hashes', return_value={}))
            stack.enter_context(patch.object(runner, 'upstream_checkout'))
            stack.enter_context(patch.object(runner, 'verify_dependency_pins'))
            preflight = stack.enter_context(patch.object(runner, 'verify_prepared_dependencies',
                side_effect=preflight_error, return_value={'status': 'pass'}))
            stack.enter_context(patch.object(runner, 'dependency_evidence', return_value={}))
            stack.enter_context(patch.object(runner.subprocess, 'check_output', return_value=''))
            stack.enter_context(redirect_stdout(io.StringIO()))
            stack.enter_context(redirect_stderr(io.StringIO()))
            code = runner.main(flags if jobs is None else [*flags, '--control-jobs', str(jobs)])
            reports = list((root / 'artifacts/certificates/lean').glob('*/manifest.json'))
            self.assertEqual(len(reports), 1)
            report = json.loads(reports[0].read_text())
            return code, calls, report, preflight.call_count

    def test_reuse_preserves_entire_verification_scope(self):
        normal = self.run_workflow([])
        reuse = self.run_workflow(['--reuse-dependencies'])
        setup = {'bootstrap', 'resolve', 'prepare-diagonal', 'mathlib-cache'}
        self.assertEqual(normal[0], 0)
        self.assertEqual(reuse[0], 0)
        self.assertEqual([s for s in normal[1] if s not in setup], reuse[1])
        self.assertTrue(setup <= set(normal[1]))
        self.assertEqual(normal[2]['verification_scope'], reuse[2]['verification_scope'])
        self.assertEqual(reuse[2]['dependency_mode'], 'reuse')
        self.assertTrue(reuse[2]['bootstrap_skipped'])
        self.assertEqual(reuse[3], 1)
        for required in ['upstream-comparator', 'pair-exact-comparator', 'project-build',
                         'axioms', 'pair-regressions', 'triple-regressions', 'harness-regressions']:
            self.assertIn(required, reuse[1])

    def test_focused_modes_remain_focused(self):
        for flag, suite in [('--zeta23-only', 'zeta23-counting-comparator'),
                            ('--pair-zero-only', 'pair-zero-comparator'),
                            ('--pair-zero-bounds-only', 'pair-zero-bounds-comparator'),
                            ('--pair-zero-comparison-only', 'pair-zero-comparison-comparator'),
                            ('--pair-asymptotic-only', 'pair-asymptotic-comparator'),
                            ('--pair-fourier-only', 'pair-fourier-comparator'),
                            ('--triple-master-only', 'triple-master-comparator'),
                            ('--triple-budget-only', 'triple-budget-comparator'),
                            ('--triple-mixed-diagonal-only', 'triple-mixed-diagonal-comparator'),
                            ('--triple-smoothing-only', 'triple-smoothing-comparator'),
                            ('--triple-resonance-decay-only', 'triple-resonance-decay-comparator'),
                            ('--triple-retained-only', 'triple-retained-comparator'),
                            ('--triple-interior-vanishing-only', 'triple-interior-vanishing-comparator'),
                            ('--triple-test-function-only', 'triple-test-function-comparator'),
                            ('--triple-boundary-only', 'triple-boundary-comparator'),
                            ('--triple-signed-sectors-only', 'triple-signed-sectors-comparator'),
                            ('--triple-kernel-localization-only', 'triple-kernel-localization-comparator')]:
            with self.subTest(flag=flag):
                code, calls, report, checked = self.run_workflow(['--reuse-dependencies', flag])
                self.assertEqual(code, 0)
                self.assertEqual(checked, 1)
                self.assertIn(suite, calls)
                if flag == '--triple-kernel-localization-only':
                    for control in ['translation', 'decomposition']:
                        self.assertIn('triple-kernel-localization-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-kernel-localization-regressions', calls)
                else:
                    self.assertNotIn('triple-kernel-localization-comparator', calls)
                if flag == '--triple-signed-sectors-only':
                    for control in ['reflection', 'interchange', 'support', 'conjugation', 'normalization', 'limit']:
                        self.assertIn('triple-signed-sectors-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-signed-sectors-regressions', calls)
                else:
                    self.assertNotIn('triple-signed-sectors-comparator', calls)
                if flag == '--triple-boundary-only':
                    for control in ['interchange', 'budget', 'origin', 'axis', 'limit', 'distribution']:
                        self.assertIn('triple-boundary-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-boundary-regressions', calls)
                else:
                    self.assertNotIn('triple-boundary-comparator', calls)
                if flag == '--triple-test-function-only':
                    for control in ['regularity', 'interchange', 'bound', 'limit']:
                        self.assertIn('triple-test-function-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-test-function-regressions', calls)
                else:
                    self.assertNotIn('triple-test-function-comparator', calls)
                if flag == '--triple-interior-vanishing-only':
                    for control in ['retained', 'observable', 'limit']:
                        self.assertIn('triple-interior-vanishing-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-interior-vanishing-regressions', calls)
                else:
                    self.assertNotIn('triple-interior-vanishing-comparator', calls)
                if flag == '--triple-retained-only':
                    for control in ['identity', 'diagonal', 'evaluation']:
                        self.assertIn('triple-retained-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-retained-regressions', calls)
                else:
                    self.assertNotIn('triple-retained-comparator', calls)
                if flag == '--triple-resonance-decay-only':
                    for control in ['count', 'summability', 'decay']:
                        self.assertIn('triple-resonance-decay-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-resonance-decay-regressions', calls)
                else:
                    self.assertNotIn('triple-resonance-decay-comparator', calls)
                if flag == '--triple-smoothing-only':
                    for control in ['identity', 'sharp']:
                        self.assertIn('triple-smoothing-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-smoothing-regressions', calls)
                else:
                    self.assertNotIn('triple-smoothing-comparator', calls)
                if flag == '--triple-mixed-diagonal-only':
                    for control in ['finite', 'asymptotic', 'endpoints']:
                        self.assertIn('triple-mixed-diagonal-' + control + '-unfinished-rejected', calls)
                    self.assertIn('triple-mixed-diagonal-regressions', calls)
                else:
                    self.assertNotIn('triple-mixed-diagonal-comparator', calls)
                if flag == '--triple-budget-only':
                    for control in ['accounting', 'refinement', 'gap', 'offdiag', 'asymptotic', 'limit']:
                        self.assertIn('triple-budget-' + control + '-unfinished-rejected', calls)
                else:
                    self.assertNotIn('triple-budget-comparator', calls)
                if flag == '--triple-master-only':
                    self.assertIn('triple-master-identity-unfinished-rejected', calls)
                    self.assertIn('triple-master-patterns-unfinished-rejected', calls)
                    self.assertIn('triple-master-expansion-unfinished-rejected', calls)
                    self.assertIn('triple-master-prime-fourier-unfinished-rejected', calls)
                    self.assertIn('triple-master-resonance-classification-unfinished-rejected', calls)
                    self.assertIn('triple-master-resonance-split-unfinished-rejected', calls)
                    self.assertIn('triple-master-fourier-decay-unfinished-rejected', calls)
                    self.assertIn('triple-master-cubic-decay-unfinished-rejected', calls)
                    self.assertIn('triple-master-assembly-unfinished-rejected', calls)
                    self.assertIn('triple-master-uniform-unfinished-rejected', calls)
                    self.assertNotIn('pair-fourier-comparator', calls)
                else:
                    self.assertNotIn('triple-master-comparator', calls)
                if flag in ['--pair-fourier-only', '--triple-master-only', '--triple-budget-only', '--triple-mixed-diagonal-only', '--triple-smoothing-only', '--triple-resonance-decay-only', '--triple-retained-only', '--triple-interior-vanishing-only', '--triple-test-function-only', '--triple-boundary-only', '--triple-signed-sectors-only', '--triple-kernel-localization-only']:
                    self.assertNotIn('pair-asymptotic-comparator', calls)
                else:
                    self.assertNotIn('pair-fourier-comparator', calls)
                if flag in ['--pair-asymptotic-only', '--pair-fourier-only', '--triple-master-only', '--triple-budget-only', '--triple-mixed-diagonal-only', '--triple-smoothing-only', '--triple-resonance-decay-only', '--triple-retained-only', '--triple-interior-vanishing-only', '--triple-test-function-only', '--triple-boundary-only', '--triple-signed-sectors-only', '--triple-kernel-localization-only']:
                    self.assertNotIn('pair-zero-comparison-comparator', calls)
                self.assertNotIn('resolve', calls)
                self.assertNotIn('upstream-comparator', calls)
                if flag in ['--pair-zero-comparison-only', '--pair-asymptotic-only', '--pair-fourier-only', '--triple-master-only', '--triple-budget-only', '--triple-mixed-diagonal-only', '--triple-smoothing-only', '--triple-resonance-decay-only', '--triple-retained-only', '--triple-interior-vanishing-only', '--triple-test-function-only', '--triple-boundary-only', '--triple-signed-sectors-only', '--triple-kernel-localization-only']:
                    self.assertNotIn('pair-zero-bounds-comparator', calls)
                    self.assertNotIn('pair-zero-comparator', calls)
                    self.assertNotIn('zeta23-counting-comparator', calls)
                self.assertIn('Earlier Comparator suites are not rerun', report['verification_scope'])

    def test_parallel_preserves_full_and_focused_scope(self):
        for flags in [['--reuse-dependencies'],
                      ['--reuse-dependencies', '--triple-kernel-localization-only']]:
            serial = self.run_workflow(flags)
            parallel = self.run_workflow(flags, jobs=4)
            self.assertEqual(parallel[0], 0)
            self.assertEqual(set(serial[1]), set(parallel[1]) - {'rejection-controls-prebuild'})
            self.assertEqual(serial[2]['verification_scope'], parallel[2]['verification_scope'])
            expected = [n for n in serial[1] if n.endswith('unfinished-rejected')]
            actual = [e['name'] for e in parallel[2]['commands'] if e.get('expected_failure')]
            self.assertEqual(actual, expected)
            prebuild = parallel[1].index('rejection-controls-prebuild')
            self.assertTrue(all(parallel[1].index(n) > prebuild for n in expected))
            self.assertTrue(all(parallel[1].index(n) < parallel[1].index('project-build') for n in expected))
            self.assertLess(parallel[1].index('project-build'), parallel[1].index('axioms'))
            self.assertEqual(parallel[2]['rejection_controls']['effective_jobs'], 4)

    def test_default_concurrency_cpu_cap_and_argument_validation(self):
        default = self.run_workflow(['--reuse-dependencies', '--triple-kernel-localization-only'], jobs=None)
        self.assertEqual(default[0], 0)
        self.assertEqual(default[2]['rejection_controls']['effective_jobs'], 4)
        capped = self.run_workflow(['--reuse-dependencies'], jobs=99)
        self.assertEqual(capped[0], 0)
        self.assertEqual(capped[2]['rejection_controls']['requested_jobs'], 99)
        self.assertEqual(capped[2]['rejection_controls']['effective_jobs'], 32)
        for invalid in ['0', '-1', 'many']:
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                runner.main(['--control-jobs', invalid])
            self.assertEqual(error.exception.code, 2)

    def test_pool_failure_and_interruption_are_archived(self):
        for error, code, status in [(RuntimeError('pool failure'), 1, 'fail'),
                                    (KeyboardInterrupt(), 130, 'interrupted')]:
            result, calls, report, _ = self.run_workflow(
                ['--reuse-dependencies', '--triple-kernel-localization-only'], jobs=4, pool_error=error)
            self.assertEqual(result, code)
            self.assertEqual(report['status'], status)
            self.assertNotIn('axioms', calls)
            controls = [e for e in report['commands'] if e.get('expected_failure')]
            self.assertEqual(len(controls), 29)
            self.assertTrue(all(e['status'] == 'cancelled' for e in controls))

    def test_preflight_failure_prevents_build_and_is_archived(self):
        code, calls, report, _ = self.run_workflow(['--reuse-dependencies'],
                                                   preflight_error=RuntimeError('missing dependency'))
        self.assertEqual(code, 1)
        self.assertEqual(calls, [])
        self.assertEqual(report['status'], 'fail')
        self.assertIn('missing dependency', report['error'])

    def test_interruption_is_archived_and_returns_130(self):
        code, calls, report, _ = self.run_workflow(['--reuse-dependencies'], interrupt=True)
        self.assertEqual(code, 130)
        self.assertEqual(report['status'], 'interrupted')
        self.assertEqual(report['commands'][-1]['status'], 'interrupted')
        self.assertEqual(calls, ['lean-version'])
        self.assertIn('finished_utc', report)

    def test_missing_upstream_never_clones(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(runner, 'ROOT', Path(tmp)), \
                patch.object(runner, 'upstream_checkout') as clone:
            with self.assertRaisesRegex(RuntimeError, 'Missing OAI checkout'):
                runner.verify_dependency_pins()
            clone.assert_not_called()

    def test_missing_and_mismatched_dependency(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(runner, 'ROOT', Path(tmp)), \
                patch.object(runner, 'verify_upstream_checkout'):
            root = Path(tmp)
            manifest = dict(packagesDir='deps', packages=[dict(name='mathlib', type='git',
                            rev=runner.PINS['upstream']['mathlib_rev'])])
            (root / 'lake-manifest.json').write_text(json.dumps(manifest))
            with patch.object(runner.subprocess, 'check_output', return_value=json.dumps(manifest)):
                with self.assertRaisesRegex(RuntimeError, 'missing dependency checkout'):
                    runner.verify_dependency_pins()
            (root / 'deps/mathlib/.git').mkdir(parents=True)
            with patch.object(runner.subprocess, 'check_output', side_effect=[json.dumps(manifest), 'wrong-revision']):
                with self.assertRaisesRegex(RuntimeError, 'disagrees with lockfile'):
                    runner.verify_dependency_pins()

    def test_patch_and_pnt_preflight_is_read_only(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            root = Path(tmp)
            tools = root / '.tools'
            deps = root / 'deps'
            upstream = root / '.lake/packages/OAI'
            patchfile = upstream / 'lean/patches/example-lean4341.patch'
            patchfile.parent.mkdir(parents=True)
            patchfile.write_text('diff --git a/value b/value\n--- a/value\n+++ b/value\n@@ -1 +1 @@\n-before\n+after\n')
            package = deps / 'example'
            package.mkdir(parents=True)
            subprocess.run(['git', 'init', '-q', str(package)], check=True)
            value = package / 'value'
            value.write_text('after\n')
            target = deps / 'PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/MediumPNT.lean'
            target.parent.mkdir(parents=True)
            prepared = ''.join(new for _, new in REPLACEMENTS)
            target.write_text(prepared)
            (root / 'lake-manifest.json').write_text(json.dumps(dict(packagesDir='deps',
                packages=[dict(name=n, type='git') for n in ['example', 'PrimeNumberTheoremAnd']])))
            binaries = ['elan/bin/elan', 'elan/bin/lean', 'elan/bin/lake', 'go/bin/go', 'bin/landrun',
                        'comparator/.lake/build/bin/comparator',
                        'comparator/.lake/packages/lean4export/.lake/build/bin/lean4export']
            for relative in binaries:
                binary = tools / relative
                binary.parent.mkdir(parents=True, exist_ok=True)
                binary.write_text('#!/bin/sh\necho /fixture/lean\n')
                binary.chmod(0o755)
            stack.enter_context(patch.object(runner, 'ROOT', root))
            stack.enter_context(patch.object(runner, 'TOOLS', tools))
            stack.enter_context(patch.object(runner, 'verify_dependency_pins'))
            stack.enter_context(patch.object(runner.subprocess, 'check_output',
                return_value='lean/patches/example-lean4341.patch\n'))
            self.assertEqual(runner.verify_prepared_dependencies()['status'], 'pass')
            self.assertEqual(value.read_text(), 'after\n')
            self.assertEqual(target.read_text(), prepared)
            value.write_text('before\n')
            with self.assertRaisesRegex(RuntimeError, 'required compatibility patch'):
                runner.verify_prepared_dependencies()
            self.assertEqual(value.read_text(), 'before\n')
            value.write_text('after\n')
            target.write_text('unprepared\n')
            with self.assertRaisesRegex(RuntimeError, 'PNT smoothing adapter'):
                runner.verify_prepared_dependencies()
            self.assertEqual(target.read_text(), 'unprepared\n')
            target.write_text(prepared)
            (tools / 'bin/landrun').chmod(0o644)
            with self.assertRaisesRegex(RuntimeError, 'Missing executable'):
                runner.verify_prepared_dependencies()

    def test_command_logging_and_negative_control(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()) as console:
            root = Path(tmp)
            report = {'commands': []}
            text = runner.run_command(root, report, 'success', [sys.executable, '-c', 'print("visible")'])
            self.assertIn('visible', text)
            self.assertIn('tail -f', console.getvalue())
            self.assertGreaterEqual(report['commands'][-1]['duration_seconds'], 0)
            runner.run_command(root, report, 'negative', [sys.executable, '-c',
                'print("Illegal axiom detected: \'sorryAx\'"); raise SystemExit(1)'], expected_failure=True)
            with self.assertRaisesRegex(RuntimeError, 'did not reject'):
                runner.run_command(root, report, 'false-negative', [sys.executable, '-c',
                    'raise SystemExit(1)'], expected_failure=True)
            self.assertEqual(report['commands'][-1]['status'], 'fail')

    def test_interrupt_terminates_process_group_and_records_stage(self):
        with tempfile.TemporaryDirectory() as tmp, redirect_stdout(io.StringIO()), \
                patch.object(runner.subprocess, 'Popen') as popen, \
                patch.object(runner.os, 'killpg') as kill:
            process = popen.return_value
            process.pid = 12345
            process.wait.side_effect = [KeyboardInterrupt, -signal.SIGTERM]
            process.returncode = -signal.SIGTERM
            report = {'commands': []}
            with self.assertRaises(KeyboardInterrupt):
                runner.run_command(Path(tmp), report, 'interrupted', ['fixture'])
            kill.assert_called_once_with(12345, signal.SIGTERM)
            self.assertTrue(popen.call_args.kwargs['start_new_session'])
            self.assertEqual(report['commands'][0]['status'], 'interrupted')
            self.assertEqual(report['commands'][0]['exit_code'], -signal.SIGTERM)


if __name__ == '__main__':
    unittest.main()
