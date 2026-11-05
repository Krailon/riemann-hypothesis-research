"""Bounded, isolated Comparator rejection controls (no proof-checker changes)."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from datetime import datetime, timezone
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import threading
import time


REJECTION = "Illegal axiom detected: 'sorryAx'"


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def available_cpus():
    try:
        return len(os.sched_getaffinity(0))
    except AttributeError:
        return os.cpu_count() or 1


def control_entry(name, argv):
    return dict(name=name, argv=list(map(str, argv)), exit_code=None,
                log=name + '.log', expected_failure=True, status='queued')


def cancel_queued(entries):
    for entry in entries:
        if entry['status'] == 'queued':
            entry.update(status='cancelled', error='Verification stopped before execution')


def tree_size(path):
    return sum(p.stat().st_size for p in path.rglob('*') if p.is_file())


def copy_tree(source, target):
    # GNU cp clones where supported, otherwise makes independent physical copies.
    # Do not use hardlinks: Lake may rewrite build outputs in place.
    subprocess.run(['cp', '-a', '--reflink=auto', str(source), str(target)], check=True)


def prepare_workers(root, scratch, jobs, metadata):
    build = root / '.lake/build'
    if not build.is_dir():
        raise RuntimeError('Missing prepared project build for rejection controls')
    size = tree_size(build) + tree_size(root / 'lean')
    reserve = 1024 ** 3
    required = jobs * size + reserve
    free = shutil.disk_usage(scratch).free
    metadata.update(seed_bytes=size, required_free_bytes=required, available_free_bytes=free,
                    copy_mode='cp -a --reflink=auto (ordinary copies on fallback)')
    if free < required:
        raise RuntimeError(f'Rejection controls need {required} free bytes; have {free}. '
                           'Reduce --control-jobs (1 uses the original serial workflow).')
    workers = []
    for index in range(jobs):
        worker = scratch / f'worker-{index + 1}'
        worker.mkdir()
        for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
            shutil.copy2(root / name, worker / name)
        copy_tree(root / 'lean', worker / 'lean')
        (worker / '.lake').mkdir()
        (worker / '.lake/packages').symlink_to(root / '.lake/packages', target_is_directory=True)
        copy_tree(build, worker / '.lake/build')
        workers.append(worker)
    return workers


def group_rss(groups):
    """Sample summed Linux RSS per process group; shared pages may be counted twice."""
    totals = dict.fromkeys(groups, 0)
    page_size = os.sysconf('SC_PAGE_SIZE')
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            fields = path.read_text().rsplit(')', 1)[1].split()
            group = int(fields[2])
            if group in totals:
                totals[group] += int(fields[21]) * page_size
        except (OSError, ValueError, IndexError):
            continue  # Process exited while sampling.
    return totals


def signal_group(pid, sig):
    try:
        os.killpg(pid, sig)
    except ProcessLookupError:
        pass


def execute_controls(entries, workers, run_dir, env, metadata):
    """Each thread owns one build tree. Main thread handles signals and cancellation."""
    lock = threading.Lock()
    stopped = threading.Event()
    pending = iter(entries)
    active = {}
    all_groups = set()
    metadata.update(status='running', peak_active_controls=0, sampled_peak_rss_bytes=0,
                    memory_measurement='Linux /proc RSS summed over active process groups, '
                    'sampled every 0.5s; shared pages may be counted twice; not a hard peak bound',
                    workers=[dict(id=i + 1, directory=str(w), sampled_peak_rss_bytes=0)
                             for i, w in enumerate(workers)])

    def worker_loop(index, directory):
        while True:
            with lock:
                if stopped.is_set():
                    return
                entry = next(pending, None)
                if entry is None:
                    return
                entry.update(worker=index + 1, cwd=str(directory), status='running',
                             started_utc=utc_now(), sampled_peak_rss_bytes=0)
            started = time.monotonic()
            process = None
            try:
                with (run_dir / entry['log']).open('w') as output:
                    with lock:
                        if stopped.is_set():
                            entry['status'] = 'cancelled'
                            return
                        process = subprocess.Popen(entry['argv'], cwd=directory, env=env,
                            stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
                        active[process.pid] = (process, entry, index)
                        all_groups.add(process.pid)
                        metadata['peak_active_controls'] = max(metadata['peak_active_controls'], len(active))
                    entry['exit_code'] = process.wait()
                if stopped.is_set():
                    entry['status'] = 'cancelled'
                    return
                text = (run_dir / entry['log']).read_text(errors='replace')
                if entry['exit_code'] == 0 or REJECTION not in text:
                    raise RuntimeError(f'{entry["name"]}: did not reject the unfinished proof for sorryAx; '
                                       f'see {run_dir / entry["log"]}')
                entry['status'] = 'pass'
            except BaseException as exc:
                entry.update(status='fail', error=str(exc))
                stopped.set()
                raise
            finally:
                with lock:
                    if process is not None:
                        # Retire the group immediately, including any descendants
                        # left by an exited leader. Do not retain stale PGIDs that
                        # the OS could reuse during a long verification batch.
                        signal_group(process.pid, signal.SIGKILL)
                        process.wait()
                        all_groups.discard(process.pid)
                        active.pop(process.pid, None)
                entry.update(finished_utc=utc_now(), duration_seconds=round(time.monotonic() - started, 3))
                print(f'{entry["name"]}: {entry["status"]} ({entry["duration_seconds"]:.1f}s)', flush=True)

    pool = ThreadPoolExecutor(max_workers=len(workers))
    futures = []
    try:
        futures = [pool.submit(worker_loop, i, directory) for i, directory in enumerate(workers)]
        remaining = set(futures)
        while remaining:
            done, remaining = wait(remaining, timeout=0.5, return_when=FIRST_COMPLETED)
            for future in done:
                future.result()
            with lock:
                snapshot = dict(active)
            rss = group_rss(snapshot)
            metadata['sampled_peak_rss_bytes'] = max(metadata['sampled_peak_rss_bytes'], sum(rss.values()))
            for pid, value in rss.items():
                _, entry, index = snapshot[pid]
                entry['sampled_peak_rss_bytes'] = max(entry['sampled_peak_rss_bytes'], value)
                worker = metadata['workers'][index]
                worker['sampled_peak_rss_bytes'] = max(worker['sampled_peak_rss_bytes'], value)
        metadata['status'] = 'pass'
    except KeyboardInterrupt:
        metadata['status'] = 'interrupted'
        raise
    except BaseException:
        metadata['status'] = 'fail'
        raise
    finally:
        stopped.set()
        # Include groups whose leader exited: surviving descendants must not retain
        # the scratch tree. Workers cannot spawn again after acquiring this lock.
        with lock:
            for pid in all_groups:
                signal_group(pid, signal.SIGTERM)
        deadline = time.monotonic() + 5
        while any(not f.done() for f in futures) and time.monotonic() < deadline:
            time.sleep(0.05)
        with lock:
            for pid in all_groups:
                signal_group(pid, signal.SIGKILL)
        pool.shutdown(wait=True, cancel_futures=True)
        cancel_queued(entries)


def run_control_pool(root, run_dir, entries, jobs, env, metadata):
    started = time.monotonic()
    metadata.update(started_utc=utc_now(), status='preparing', control_count=len(entries),
                    effective_jobs=min(jobs, len(entries)))
    print(f'rejection-controls: {len(entries)} controls, {metadata["effective_jobs"]} workers', flush=True)
    try:
        # Sibling trees on the same filesystem, never included in certificate archives.
        with tempfile.TemporaryDirectory(prefix='rejection-controls-', dir=root / '.lake') as tmp:
            scratch = Path(tmp)
            metadata['scratch_directory'] = str(scratch)
            workers = prepare_workers(root, scratch, metadata['effective_jobs'], metadata)
            metadata['setup_seconds'] = round(time.monotonic() - started, 3)
            execution_started = time.monotonic()
            try:
                execute_controls(entries, workers, run_dir, env, metadata)
            finally:
                metadata['execution_seconds'] = round(time.monotonic() - execution_started, 3)
    except KeyboardInterrupt:
        metadata['status'] = 'interrupted'
        raise
    except BaseException as exc:
        metadata.update(status='fail', error=str(exc))
        raise
    finally:
        cancel_queued(entries)
        metadata.update(finished_utc=utc_now(), duration_seconds=round(time.monotonic() - started, 3),
                        scratch_cleaned=not Path(metadata.get('scratch_directory', '/')).exists())
