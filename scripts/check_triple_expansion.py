#!/usr/bin/env python3
"""UNCONDITIONAL finite bookkeeping check connecting Lean's literal word table
with both existing manuscript tables. The analytic identity is checked by Lean.
"""
from itertools import product
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class TripleExpansionChecks(unittest.TestCase):
    def test_lean_ordered_table_matches_both_manuscript_tables(self):
        lean = (ROOT / 'lean/HigherCorrelations/TripleExpansionDefinitions.lean').read_text()
        md = (ROOT / 'research/triple-master-bookkeeping.md').read_text()
        tex = (ROOT / 'proofs/triple_explicit_formula.tex').read_text()
        lean_rows = re.findall(
            r'^  \(!\[\.([PAH]),\.([PAH]),\.([PAH])\], (-?1), (true|false)\)[,\]]',
            lean, re.M)
        expected = [(''.join(w), '-' if w.count('P') % 2 else '+',
                     'yes' if 'H' in w else 'no') for w in product('PAH', repeat=3)]
        self.assertEqual(
            [(''.join(row[:3]), '-' if row[3] == '-1' else '+',
              'yes' if row[4] == 'true' else 'no') for row in lean_rows], expected)
        md_rows = re.findall(
            r'^\| ([PAH]{3}) \| ([+-]) \| \\\((.*?)\\\) \| (yes|no) \|$', md, re.M)
        tex_rows = re.findall(
            r'^([PAH]{3}) & \$([+-])\$ & \$(.*?)\$ & (yes|no)\\\\$', tex, re.M)
        for rows in (md_rows, tex_rows):
            self.assertEqual([(row[0], row[1], row[3]) for row in rows], expected)
            for word, _, integrand, _ in rows:
                self.assertEqual(integrand,
                                 word[0]+'_X'+word[1]+'_Y'+r'\overline{'+word[2]+'_Z}')


if __name__ == '__main__':
    unittest.main()
