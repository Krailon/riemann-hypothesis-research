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
    def run_workflow(self, flags, *, interrupt=False, preflight_error=None):
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
            code = runner.main(flags)
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
                            ('--pair-fourier-only', 'pair-fourier-comparator')]:
            with self.subTest(flag=flag):
                code, calls, report, checked = self.run_workflow(['--reuse-dependencies', flag])
                self.assertEqual(code, 0)
                self.assertEqual(checked, 1)
                self.assertIn(suite, calls)
                if flag == '--pair-fourier-only':
                    self.assertNotIn('pair-asymptotic-comparator', calls)
                else:
                    self.assertNotIn('pair-fourier-comparator', calls)
                if flag in ['--pair-asymptotic-only', '--pair-fourier-only']:
                    self.assertNotIn('pair-zero-comparison-comparator', calls)
                self.assertNotIn('resolve', calls)
                self.assertNotIn('upstream-comparator', calls)
                if flag in ['--pair-zero-comparison-only', '--pair-asymptotic-only', '--pair-fourier-only']:
                    self.assertNotIn('pair-zero-bounds-comparator', calls)
                    self.assertNotIn('pair-zero-comparator', calls)
                    self.assertNotIn('zeta23-counting-comparator', calls)
                self.assertIn('Earlier Comparator suites are not rerun', report['verification_scope'])

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
