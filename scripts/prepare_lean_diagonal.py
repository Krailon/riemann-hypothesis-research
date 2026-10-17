#!/usr/bin/env python3
"""Restore the pinned PNT smoothing input omitted by its compatibility port.

Only redirect MediumPNT to the namespaced, proved copy already shipped at the
same dependency revision. Run after OAI's compatibility hook and before building.
The reproduction manifest archives the resulting dependency diff.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / '.lake/packages/OAI/lean/.lake/packages/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/MediumPNT.lean'
REPLACEMENTS = (
    ('import PrimeNumberTheoremAnd.SmoothExistence\n',
     'import PrimeNumberTheoremAnd.SmoothExistence\nimport PrimeNumberTheoremAnd.Erdos970.SmoothExistence\n'),
    ('ν_massOne\'⟩ := SmoothExistence\n', 'ν_massOne\'⟩ := Erdos970.SmoothExistence\n'),
)


def prepare():
    original = TARGET.read_text()
    text = original
    for old, new in REPLACEMENTS:
        if text.count(new) == 1:
            continue
        if text.count(old) != 1:
            raise RuntimeError('Unexpected MediumPNT source; refusing compatibility rewrite')
        text = text.replace(old, new)
    if text != original:
        TARGET.write_text(text)
    print('PNT smoothing compatibility input ready')


if __name__ == '__main__':
    prepare()
