#!/usr/bin/env python3
"""Check the selected Zeta23 source pin, hashes and exact compatibility diff.

This checks provenance, not mathematical correctness; Lean and Comparator supply
the proof checks. Original sources are immutable after initial import.
"""
import difflib
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'vendor/zeta23'


def check():
    record = json.loads((BASE / 'manifest.json').read_text())
    assert record['rev'] == 'e1a4e6508154ea59f030480661590a9fe3018011'
    assert record['upstream'] == 'https://github.com/anthropics/formal-math'
    pins = json.loads((ROOT/'research/lean-import-pins.json').read_text())['zeta23']
    assert pins['rev'] == record['rev'] and pins['url'] == record['upstream']
    assert pins['original_lean'] == (BASE/'lean-toolchain').read_text().strip()
    upstream_packages = json.loads((BASE/'lake-manifest.json').read_text())['packages']
    assert pins['original_mathlib_rev'] == next(p['rev'] for p in upstream_packages if p['name'] == 'mathlib')
    patches = []
    imports = {}
    actual = set()
    for name, entry in record['modules'].items():
        original, port = ROOT / entry['upstream'], ROOT / entry['source']
        raw, edited = original.read_bytes(), port.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == entry['upstream_sha256'], name
        assert hashlib.sha256(edited).hexdigest() == entry['ported_sha256'], name
        patches.extend(difflib.unified_diff(raw.decode().splitlines(True),
                       edited.decode().splitlines(True),
                       fromfile=entry['upstream'], tofile=entry['source']))
        imports[name] = [d for line in re.findall(r'^import\s+([^\n]+)', raw.decode(), re.M)
                         for d in line.split() if d.startswith('Zeta23.')]
        actual.add(str(port.relative_to(ROOT)))
    seen, todo = set(), list(record['roots'])
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo.extend(imports[name])
    assert seen == set(record['modules']), 'Selected source closure changed'
    assert actual == {str(p.relative_to(ROOT)) for p in (ROOT/'lean/Zeta23').rglob('*.lean')}
    assert ''.join(patches) == (BASE/'compatibility.patch').read_text(), 'Unrecorded port patch'
    for path, expected in record['metadata_sha256'].items():
        assert hashlib.sha256((BASE/path).read_bytes()).hexdigest() == expected, path
    print(f'Zeta23 provenance: {len(seen)} modules, exact patches and metadata verified')


if __name__ == '__main__':
    check()
