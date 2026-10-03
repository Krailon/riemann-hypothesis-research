#!/usr/bin/env python3
"""Finite exact checks: UNCONDITIONAL algebra; SYNTHETIC_MODEL fixtures.

No zero data, floating point, asymptotic verification or proof certificate.
Polynomial tests and rational scales below check finite identities only.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G
from check_pair_rh_audit import field, indexed_blocks
from check_triple_kernel import centers, profile

ROOT = Path(__file__).resolve().parents[1]


def fixture():
    positive = [(Q(-1, 4), Q(3)), (Q(1, 4), Q(3))] * 2
    positive += [(Q(0), Q(5))]
    return positive + [(delta, -gamma) for delta, gamma in positive]


def polynomial(u, v):
    return 1 + u + G(0, 1)*v + u*u + u*v


def terms(triple):
    (e1, g1), (e2, g2), (e3, g3) = triple
    a, d = g2-g1, g3-g1
    ell = Q(3, 2)  # Formal scale; no approximation to pi or logarithms.
    u, v = G(ell*a), G(ell*d)
    z1, z2 = u + G(0, -ell*(e2+e1)), v + G(0, -ell*(e3+e1))
    j = profile(centers(a, d, (e2, e3, e1)))  # J/pi
    j0 = profile(centers(a, d, (0, 0, 0)))
    f, fz = polynomial(u, v), polynomial(z1, z2)
    return j*fz, Q(3, 8)*f, j*(fz-f), (j-j0)*f, (j0-Q(3, 8))*f


class OrdinateReductionChecks(unittest.TestCase):
    def test_telescope_with_collisions_and_repeated_occurrences(self):
        totals = [G() for _ in range(5)]
        for triple in product(fixture(), repeat=3):
            if triple[0][1] <= 0:
                continue
            values = terms(triple)
            self.assertEqual(values[0], sum(values[1:], G()))
            totals = [a+b for a, b in zip(totals, values)]
        self.assertEqual(totals[0], sum(totals[1:], G()))
        self.assertNotEqual(totals[2], G())

    def test_normalization_and_main_term_error_signs(self):
        # p represents pi as a formal nonzero scalar; ell=b/(2p).
        for p, b, q, t in [(Q(7, 2), Q(4), Q(6), Q(19)),
                           (Q(3), Q(11), Q(13), Q(101))]:
            ell = b/(2*p)
            c = Q(16)/(3*t*q)
            self.assertEqual(c*(3*p/8), (b/q)/(t*ell))
            o, main, ea, eh, eg = map(Q, [7, 3, 2, -5, 11])
            weighted = b/q*o + ea + eh + eg
            self.assertEqual(o-main, q/b*(weighted-main-ea-eh-eg)
                             + (q/b-1)*main)

    def test_full_reflection_preserves_occurrences_and_partitions(self):
        zeros = fixture()
        self.assertEqual(Counter(zeros), Counter((-e, g) for e, g in zeros))
        # A concrete permutation retains copies, not just the set of zeros.
        reflection = [1, 0, 3, 2, 4, 6, 5, 8, 7, 9]
        for ids in product(range(len(zeros)), repeat=3):
            reflected = tuple(reflection[i] for i in ids)
            for j, k in [(0, 1), (0, 2), (1, 2)]:
                self.assertEqual(ids[j] == ids[k], reflected[j] == reflected[k])
            for i, ri in zip(ids, reflected):
                self.assertEqual(zeros[ri], (-zeros[i][0], zeros[i][1]))

    def test_kernel_reflection_including_closed_parameter_endpoints(self):
        for a, d in [(0, 0), (Q(1, 3), Q(-2, 5))]:
            for delta in product([Q(-1, 2), Q(0), Q(1, 2)], repeat=3):
                j = profile(centers(a, d, delta))
                reflected = profile(centers(a, d, tuple(-x for x in delta)))
                self.assertEqual(reflected, j.conjugate())
                self.assertEqual(((j+reflected)/2).imag, 0)
        self.assertEqual(profile(centers(0, 0, (0, 0, 0))), G(Q(3, 8)))

    def test_support_exponent_identity_in_all_sectors_and_axes(self):
        for xi, eta in product([Q(-2), Q(-1, 2), Q(0), Q(1, 2), Q(2)], repeat=2):
            h = max(abs(xi), abs(eta), abs(xi+eta))
            self.assertEqual(abs(xi)+abs(eta)+abs(xi+eta), 2*h)
            for signs in product([-1, 1], repeat=3):
                exponent = signs[1]*xi+signs[2]*eta+signs[0]*(xi+eta)
                self.assertLessEqual(abs(exponent), 2*h)

    def test_microscopic_symmetric_mode_does_not_cancel(self):
        # e^(c*b/q) is the exact formal rational base; integer frequencies
        # avoid any transcendental evaluation. This is a finite mode identity.
        base = Q(2)
        cosh = lambda k: (base**k+base**(-k))/2
        for xi, eta in [(0, 0), (1, 0), (0, -1), (1, -1), (1, 2)]:
            average = sum((base**(e2*xi+e3*eta+e1*(xi+eta))
                           for e1, e2, e3 in product([-1, 1], repeat=3)), Q())/8
            self.assertEqual(average, cosh(xi)*cosh(eta)*cosh(xi+eta))
            if (xi, eta) != (0, 0):
                self.assertGreater(average, 1)

    def test_triangle_majorizes_close_pairs_with_multiplicity(self):
        ordinates = [Q(0), Q(0), Q(1, 3), Q(2, 3), Q(2)]
        radius = Q(1, 2)
        close = sum(abs(x-y) <= radius for x, y in product(ordinates, repeat=2))
        weighted = sum((max(Q(0), 1-abs(x-y)/(2*radius))
                        for x, y in product(ordinates, repeat=2)), Q())
        self.assertLessEqual(close, 2*weighted)
        degrees = [sum(abs(x-y) <= radius for y in ordinates) for x in ordinates]
        triples = sum(degree**2 for degree in degrees)
        brute = sum(max(abs(y-x), abs(z-x)) <= radius
                    for x, y, z in product(ordinates, repeat=3))
        self.assertEqual(triples, brute)
        self.assertLessEqual(triples, max(degrees)*close)

    def test_ledger_leaves_ordinate_theorem_open(self):
        blocks = indexed_blocks((ROOT/'research/theorem-ledger.yaml').read_text())
        self.assertEqual(field(blocks['ORDINATE-TRIPLE-001'], 'status'), 'idea')
        self.assertEqual(field(blocks['ORDINATE-ARGUMENT-BOUND-001'], 'status'),
                         'proved-draft')
        self.assertIn('not proved', blocks['ORDINATE-TRIPLE-001'])
        proof = (ROOT/'proofs/triple_ordinate_reduction.tex').read_text()
        for key, block in blocks.items():
            if key.startswith('ORDINATE-'):
                label = re.search(r'^      label: (.+)$', block, re.M).group(1)
                self.assertIn('\\label{'+label+'}', proof)


if __name__ == '__main__':
    unittest.main()
