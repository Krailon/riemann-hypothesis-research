#!/usr/bin/env python3
"""UNCONDITIONAL orchestration tests, using real subprocesses, not Lean proofs."""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import unittest
from unittest.mock import patch

import lean_control_pool as pool


class ControlPoolTests(unittest.TestCase):
    def fixture(self, root):
        (root / '.lake/build').mkdir(parents=True)
        (root / '.lake/packages').mkdir()
        (root / '.lake/build/seed').write_text('original')
        (root / 'lean').mkdir()
        (root / 'lean/source.lean').write_text('original')
        for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
            (root / name).write_text('fixture')
        logs = root / 'logs'
        logs.mkdir()
        return logs

    def entry(self, name, body):
        return pool.control_entry(name, [sys.executable, '-c', body])

    def run_pool(self, root, logs, entries, jobs, metadata):
        with redirect_stdout(io.StringIO()):
            pool.run_control_pool(root, logs, entries, jobs, os.environ.copy(), metadata)

    def test_real_overlap_bound_order_and_isolation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            logs = self.fixture(root)
            entries = []
            for i in range(6):
                # The first pair cannot finish until both processes have started.
                body = f'''import json, pathlib, time
p = pathlib.Path
marker = p({str(logs / str(i))!r})
marker.write_text('started')
if {i} < 2:
    deadline = time.monotonic() + 10
    while not p({str(logs / str(1 - i))!r}).exists():
        assert time.monotonic() < deadline, 'controls did not overlap'
        time.sleep(.01)
p('.lake/build/seed').write_text('changed')
p('lean/source.lean').write_text('changed')
print(json.dumps(dict(cwd=str(p.cwd()), inode=p('.lake/build/seed').stat().st_ino)))
time.sleep(.15)
print({pool.REJECTION!r})
raise SystemExit(1)
'''
                entries.append(self.entry(str(i), body))
            metadata = {}
            self.run_pool(root, logs, entries, 2, metadata)
            self.assertEqual([e['name'] for e in entries], list(map(str, range(6))))
            self.assertTrue(all(e['status'] == 'pass' and e['exit_code'] == 1 for e in entries))
            self.assertEqual(metadata['peak_active_controls'], 2)
            self.assertEqual(metadata['effective_jobs'], 2)
            self.assertTrue(metadata['scratch_cleaned'])
            self.assertTrue(all('started_utc' in e and 'finished_utc' in e for e in entries))
            records = [json.loads((logs / e['log']).read_text().splitlines()[0]) for e in entries[:2]]
            self.assertEqual(len({r['cwd'] for r in records}), 2)
            self.assertEqual(len({r['inode'] for r in records}), 2)
            self.assertNotIn((root / '.lake/build/seed').stat().st_ino, [r['inode'] for r in records])
            self.assertEqual((root / '.lake/build/seed').read_text(), 'original')
            self.assertEqual((root / 'lean/source.lean').read_text(), 'original')

    def test_unexpected_success_and_wrong_failure_cancel_queue(self):
        for body in [f'print({pool.REJECTION!r})', 'raise SystemExit(2)']:
            with self.subTest(body=body), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                logs = self.fixture(root)
                entries = [self.entry('bad', body), self.entry('queued', 'raise SystemExit(1)')]
                metadata = {}
                with self.assertRaisesRegex(RuntimeError, 'did not reject'):
                    self.run_pool(root, logs, entries, 1, metadata)
                self.assertEqual([e['status'] for e in entries], ['fail', 'cancelled'])
                self.assertEqual(metadata['status'], 'fail')
                self.assertTrue(metadata['scratch_cleaned'])
                self.assertFalse((logs / 'queued.log').exists())

    def test_failed_control_stops_another_active_control(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            logs = self.fixture(root)
            marker = str(logs / 'active.pid')
            bad = f"""import pathlib, time
limit = time.monotonic() + 10
while not pathlib.Path({marker!r}).exists():
    assert time.monotonic() < limit
    time.sleep(.01)
print({pool.REJECTION!r})
"""
            active = f"""import os, pathlib, time
pathlib.Path({marker!r}).write_text(str(os.getpid()))
time.sleep(60)
"""
            entries = [self.entry('bad', bad), self.entry('active', active),
                       self.entry('queued', active)]
            metadata = {}
            with self.assertRaisesRegex(RuntimeError, 'did not reject'):
                self.run_pool(root, logs, entries, 2, metadata)
            self.assertEqual([e['status'] for e in entries], ['fail', 'cancelled', 'cancelled'])
            self.assertLess(entries[1]['exit_code'], 0)
            self.assertEqual(metadata['peak_active_controls'], 2)
            self.assertTrue(metadata['scratch_cleaned'])
            self.assertFalse(Path(f"/proc/{(logs / 'active.pid').read_text()}").exists())

    def test_interruption_kills_descendants_before_cleanup(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            logs = self.fixture(root)
            child = "import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(60)"
            body = f'''import pathlib, subprocess, sys, time, signal
signal.signal(signal.SIGTERM, signal.SIG_IGN)
p = subprocess.Popen([sys.executable, '-c', {child!r}])
pathlib.Path({str(logs / 'child.pid')!r}).write_text(str(p.pid))
time.sleep(60)
'''
            entries = [self.entry('active', body), self.entry('queued', body)]
            metadata = {}
            sample = pool.group_rss

            def interrupt(groups):
                if (logs / 'child.pid').exists():
                    raise KeyboardInterrupt
                return sample(groups)

            with patch.object(pool, 'group_rss', side_effect=interrupt), self.assertRaises(KeyboardInterrupt):
                self.run_pool(root, logs, entries, 1, metadata)
            self.assertEqual(metadata['status'], 'interrupted')
            self.assertTrue(metadata['scratch_cleaned'])
            self.assertEqual([e['status'] for e in entries], ['cancelled', 'cancelled'])
            self.assertEqual(entries[0]['exit_code'], -signal.SIGKILL)
            pid = int((logs / 'child.pid').read_text())
            stat = Path(f'/proc/{pid}/stat')
            if stat.exists():
                self.assertEqual(stat.read_text().rsplit(')', 1)[1].split()[0], 'Z')

    def test_low_disk_space_fails_before_copying(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            logs = self.fixture(root)
            metadata = {}
            entries = [self.entry('never', '')]
            usage = type('Usage', (), {'free': 0})()
            with patch.object(pool.shutil, 'disk_usage', return_value=usage), \
                    patch.object(pool, 'copy_tree') as copy, self.assertRaisesRegex(RuntimeError, 'Reduce --control-jobs'):
                self.run_pool(root, logs, entries, 2, metadata)
            copy.assert_not_called()
            self.assertTrue(metadata['scratch_cleaned'])
            self.assertEqual(entries[0]['status'], 'cancelled')

    def test_affinity_cap_and_fallback(self):
        with patch.object(pool.os, 'sched_getaffinity', return_value={3, 4}):
            self.assertEqual(pool.available_cpus(), 2)
        with patch.object(pool.os, 'sched_getaffinity', side_effect=AttributeError), \
                patch.object(pool.os, 'cpu_count', return_value=8):
            self.assertEqual(pool.available_cpus(), 8)


if __name__ == '__main__':
    unittest.main()
