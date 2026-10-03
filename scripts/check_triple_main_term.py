#!/usr/bin/env python3
"""Exact finite verification of the sine-benchmark comparison.

Task: verification. Assumptions: UNCONDITIONAL for algebra and conventions;
SYNTHETIC_MODEL only for repeated-occurrence fixtures. Rational grids,
polynomials and formal log/pi parameters are not asymptotic proofs or
numerical certificates. Analytic transforms are proved in the manuscript.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G, occurrences
from check_pair_rh_audit import field, id_list, indexed_blocks

ROOT = Path(__file__).resolve().parents[1]


def h(x, y):
    return max(abs(x), abs(y), abs(x+y))


def tau(x):
    return max(Q(), 1-abs(x))


def overlap(*centers):
    """Intersection length of unit intervals, independently of h."""
    return max(Q(), min(c+Q(1, 2) for c in centers)
               - max(c-Q(1, 2) for c in centers))


def planar(x, y):
    return 1-tau(x)-tau(y)-tau(x+y)+2*overlap(0, x, -y)


def partition(indices):
    blocks = {}
    for slot, index in enumerate(indices, 1):
        blocks.setdefault(index, []).append(slot)
    return '|'.join(''.join(map(str, slots)) for slots in blocks.values())


class TripleMainTermChecks(unittest.TestCase):
    def test_determinant_by_permutations(self):
        # Polynomial exponents of A=s(u), B=s(v), C=s(u-v).
        entry = {(0, 1): (1, 0, 0), (0, 2): (0, 1, 0), (1, 2): (0, 0, 1)}
        coefficients = Counter()
        for p in permutations(range(3)):
            inversions = sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
            powers = [0, 0, 0]
            for i, j in enumerate(p):
                if i != j:
                    for k, v in enumerate(entry[tuple(sorted((i, j)))]):
                        powers[k] += v
            coefficients[tuple(powers)] += (-1)**inversions
        self.assertEqual(dict(coefficients),
                         {(0, 0, 0): 1, (2, 0, 0): -1, (0, 2, 0): -1,
                          (0, 0, 2): -1, (1, 1, 1): 2})

    def test_five_occurrence_partitions_without_simplicity(self):
        for n in range(1, 7):
            counts = Counter(partition(t) for t in product(range(n), repeat=3))
            expected = {'123': n, '12|3': n*(n-1), '13|2': n*(n-1),
                        '1|23': n*(n-1), '1|2|3': n*(n-1)*(n-2)}
            self.assertEqual(counts, Counter({k: v for k, v in expected.items() if v}))
            self.assertEqual(sum(counts.values()), n**3)
        zeros = occurrences()
        i, j = next((i, j) for i in range(len(zeros)) for j in range(i+1, len(zeros))
                    if zeros[i] == zeros[j])
        self.assertEqual(partition((i, j, i)), '13|2')
        self.assertEqual(partition((zeros[i], zeros[j], zeros[i])), '123')

    def test_triangle_and_triple_interval_endpoints(self):
        grid = [Q(k, 4) for k in range(-8, 9)]
        for x in grid:
            self.assertEqual(overlap(0, x), tau(x))
            for y in grid:
                self.assertEqual(overlap(0, x, -y), max(Q(), 1-h(x, y)))
        for x, y in ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)):
            self.assertEqual(overlap(0, x, -y), 0)
            self.assertEqual(planar(x, y), 0)
        self.assertEqual(overlap(0, 0, 0), 1)

    def test_six_sectors_support_mapping_and_outside_witness(self):
        for a, b in product((Q(1, 8), Q(1, 4), Q(3, 8)), repeat=2):
            sectors = ((a, b), (-a, -b), (-a, a+b), (a+b, -a),
                       (a, -a-b), (-a-b, a))
            self.assertEqual(len(set(sectors)), 6)
            for x, y in sectors:
                self.assertEqual(h(x, y), a+b)
                vector = (-x-y, x, y)
                self.assertEqual(sum(vector), 0)
                self.assertEqual(sum(map(abs, vector)), 2*h(x, y))
                self.assertEqual(planar(x, y), 0)
                kappa = 1-h(x, y)
                epsilon = kappa  # Strict source region; epsilon < 2*kappa.
                self.assertLess(sum(map(abs, vector)), 2-epsilon)
                self.assertEqual(tuple(-r for r in vector), (x+y, -x, -y))
        self.assertEqual(planar(Q(3, 4), Q(3, 4)), Q(1, 2))

    def test_line_pushforwards_and_anchor_phase(self):
        for r, xi, eta in product((Q(-2), Q(0), Q(1, 3)), repeat=3):
            # Each physical line phase isolates its stated frequency normal.
            for (u, v), normal in (((0, r), eta), ((r, 0), xi), ((r, r), xi+eta)):
                self.assertEqual(u*xi+v*eta, r*normal)
        # u=r+w,v=w and xi=r,eta=s-r both have determinant one.
        for a, b, c, d in ((1, 1, 0, 1), (1, 0, -1, 1)):
            self.assertEqual(a*d-b*c, 1)
        for x1, x2, x3, xi, eta in product((Q(-1), Q(1, 3)), repeat=5):
            self.assertEqual((x2-x1)*xi+(x3-x1)*eta,
                             x1*(-xi-eta)+x2*xi+x3*eta)

    def test_partition_fourier_coefficients_and_cumulant_subtraction(self):
        # Independent formal basis: origin atom O, line deltas D_*,
        # triangular line densities TD_*, planar constant 1, triangles T_*, C.
        rows = [Counter({'1': 1}), Counter({'D_y': 1, 'T_y': -1}),
                Counter({'D_x': 1, 'T_x': -1}), Counter({'D_sum': 1, 'T_sum': -1}),
                Counter({'O': 1, 'TD_y': -1, 'TD_x': -1, 'TD_sum': -1, 'C': 2})]
        total = Counter()
        for row in rows:
            total.update(row)  # Counter addition would discard negative terms.
        cumulant = total.copy()
        cumulant.subtract({'O': 1, 'D_y': 1, 'D_x': 1, 'D_sum': 1,
                           'TD_y': -1, 'TD_x': -1, 'TD_sum': -1})
        self.assertEqual({k: v for k, v in cumulant.items() if v},
                         {'1': 1, 'T_y': -1, 'T_x': -1, 'T_sum': -1, 'C': 2})
        self.assertNotIn('O', rows[0])  # Physical atom transforms to density one.
        self.assertEqual(rows[-1]['O'], 1)  # R3 physical constant gives origin atom.
        self.assertEqual(2*overlap(0, 0, 0), 2)  # Factorial cycle remains nonzero.

    def test_complex_bilinear_central_inversion(self):
        # Finite symmetric pairing fixture, not quadrature of a Schwartz test.
        def phi(x, y):
            return G(1+x+2*y+x*y, 3-2*x+y+x*x)
        nodes = [(Q(k, 4), Q(1, 4)) for k in range(-3, 4)]
        def pairing(negate=False):
            total = phi(0, 0)
            for r, weight in nodes:
                for x, y in ((r, 0), (0, r), (r, -r)):
                    total += weight*abs(r)*phi(-x if negate else x, -y if negate else y)
            return total
        value = pairing()
        self.assertEqual(value, pairing(True))
        self.assertNotEqual(value, value.conjugate())
        self.assertEqual(Q(3, 2)*value*Q(2, 3), value)

    def test_finite_height_normalization_not_its_limit(self):
        # p=2*pi, q=log T, c=log(2*pi) are formal rational fixtures.
        for T, p, q, c in ((Q(100), Q(6), Q(7), Q(2)), (Q(300), Q(7), Q(11), Q(3))):
            b = q-c
            LT = b/p
            finite = 3*b/(2*q)
            self.assertEqual(8/(T*q)*(3*p/16), finite/(T*LT))
            self.assertNotEqual(finite, Q(3, 2))
            self.assertEqual(Q(3, 2)-finite, 3*c/(2*q))

    def test_claims_provenance_labels_and_links(self):
        blocks = indexed_blocks((ROOT/'research/theorem-ledger.yaml').read_text())
        tex = (ROOT/'proofs/triple_explicit_formula.tex').read_text()
        md_path = ROOT/'research/triple-main-term-comparison.md'
        md = md_path.read_text()
        claims = {
            'TRIPLE-SINE-MEASURE-001': ('lem:triple-sine-measure', set()),
            'TRIPLE-MAIN-TERM-COMPARISON-001': ('lem:triple-main-term-comparison',
                {'TRIPLE-SINE-MEASURE-001', 'TRIPLE-SIGNED-TEST-FUNCTION-001',
                 'TRIPLE-KERNEL-LOCALIZATION-001', 'TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001'})}
        for claim, (label, deps) in claims.items():
            block = blocks[claim]
            self.assertEqual(field(block, 'status'), 'proved-draft')
            self.assertEqual(field(block, 'computation_used_in_proof'), 'false')
            self.assertEqual(field(block, 'all_limit_interchanges_justified'), 'true')
            self.assertEqual(set(id_list(field(block, 'dependencies'))), deps)
            self.assertIn('UNCONDITIONAL', field(block, 'assumptions'))
            self.assertIn('label: '+label, block)
            self.assertIn(r'\label{'+label+'}', tex)
            self.assertIn(label, md)
        self.assertIn('SUPPORT(h<=1-kappa, 0<kappa<1)',
                      field(blocks['TRIPLE-MAIN-TERM-COMPARISON-001'], 'assumptions'))
        note_path = ROOT/'research/literature-notes/triple-sine-comparison.md'
        note = note_path.read_text()
        self.assertIn('Theorem 1, equation (2), manuscript p. 2', note)
        self.assertIn('arXiv:1212.5537v2', note)
        self.assertIn('No zeta theorem', note)
        self.assertIn('@article{ConreySnaith2014,', (ROOT/'research/literature.bib').read_text())
        for path in (md_path, note_path):
            for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', path.read_text()):
                if not target.startswith('https://'):
                    self.assertTrue((path.parent/target).is_file(), target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
