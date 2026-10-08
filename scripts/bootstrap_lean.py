#!/usr/bin/env python3
"""Install the pinned Linux x86_64 proof tools inside .tools, without shell edits."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / '.tools'
PINS = json.loads((ROOT / 'research/lean-import-pins.json').read_text())


def environment():
    env = os.environ.copy()
    env.update(ELAN_HOME=str(TOOLS / 'elan'), ELAN_TOOLCHAIN=PINS['lean'],
               GOPATH=str(TOOLS / 'gopath'), GOCACHE=str(TOOLS / 'gocache'),
               GOTOOLCHAIN='local', GIT_TERMINAL_PROMPT='0')
    paths = [TOOLS / 'elan/bin', TOOLS / 'go/bin', TOOLS / 'bin',
             TOOLS / 'comparator/.lake/build/bin',
             TOOLS / 'comparator/.lake/packages/lean4export/.lake/build/bin']
    env['PATH'] = os.pathsep.join(map(str, paths)) + os.pathsep + env.get('PATH', '')
    env['COMPARATOR_LANDRUN'] = str(TOOLS / 'bin/landrun')
    env['COMPARATOR_LEAN4EXPORT'] = str(paths[-1] / 'lean4export')
    return env


def run(argv, cwd=ROOT):
    print('+', ' '.join(map(str, argv)), flush=True)
    subprocess.run(list(map(str, argv)), cwd=cwd, env=environment(), check=True)


def archive(name):
    spec = PINS[name]
    downloads = TOOLS / 'downloads'
    downloads.mkdir(parents=True, exist_ok=True)
    target = downloads / (name + '.tar.gz')
    if not target.exists():
        partial = target.with_suffix('.partial')
        print('Downloading', spec['url'], flush=True)
        with urllib.request.urlopen(spec['url'], timeout=120) as source, partial.open('wb') as out:
            shutil.copyfileobj(source, out)
        partial.rename(target)
    actual = hashlib.file_digest(target.open('rb'), 'sha256').hexdigest()
    if actual != spec['sha256']:
        raise RuntimeError(f'{name}: archive checksum mismatch: {actual}')
    return target


def checkout(name, target=None):
    spec, target = PINS[name], target or TOOLS / name
    if not target.exists():
        run(['git', 'clone', '--filter=blob:none', '--no-checkout', spec['url'], target])
        run(['git', 'checkout', '--detach', spec['rev']], cwd=target)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=target, text=True).strip()
    if head != spec['rev']:
        raise RuntimeError(f'{name}: expected {spec["rev"]}, found {head}')
    if subprocess.check_output(['git', 'diff', 'HEAD', '--'], cwd=target):
        raise RuntimeError(f'{name}: tracked source differs from the pinned commit')
    return target


def upstream_checkout():
    target = ROOT / '.lake/packages/OAI'
    target.parent.mkdir(parents=True, exist_ok=True)
    return checkout('upstream', target)


def bootstrap():
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        raise RuntimeError('This pinned bootstrap supports Linux x86_64 only.')
    TOOLS.mkdir(exist_ok=True)
    (TOOLS / 'bin').mkdir(exist_ok=True)
    if not (TOOLS / 'elan/bin/elan').exists():
        installer = TOOLS / 'elan-installer'
        installer.mkdir(exist_ok=True)
        with tarfile.open(archive('elan')) as source:
            source.extractall(installer, filter='data')
        run([installer / 'elan-init', '-y', '--no-modify-path', '--default-toolchain', 'none'])
    installed = subprocess.check_output(['elan', 'toolchain', 'list'],
                                        env=environment(), text=True)
    if PINS['lean'] not in {line.split()[0] for line in installed.splitlines() if line.strip()}:
        run(['elan', 'toolchain', 'install', PINS['lean']])
    run(['lean', '--version'])
    if not (TOOLS / 'go/bin/go').exists():
        with tarfile.open(archive('go')) as source:
            source.extractall(TOOLS, filter='data')
    run(['go', 'version'])
    landrun = checkout('landrun')
    run(['go', 'build', '-o', TOOLS / 'bin/landrun', './cmd/landrun'], cwd=landrun)
    comparator = checkout('comparator')
    manifest = json.loads((comparator / 'lake-manifest.json').read_text())
    exporter = next(p for p in manifest['packages'] if p['name'] == 'lean4export')
    if exporter['rev'] != PINS['comparator']['lean4export_rev']:
        raise RuntimeError('Unexpected lean4export revision in Comparator manifest')
    # Deliberately retain the committed manifest; `lake update` would follow master.
    run(['lake', 'build', 'lean4export', 'comparator'], cwd=comparator)
    run(['landrun', '--version'])
    upstream_checkout()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    bootstrap()
