#!/usr/bin/env python3
"""Exact regression checks for one-sided boundary bookkeeping.

Task: verification. Assumptions: UNCONDITIONAL for finite algebra;
SYNTHETIC_MODEL for the inherited zero fixtures. No numerical certificate
or check of an analytic asymptotic is claimed. Standard library only.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G, I, occurrences
from check_pair_rh_audit import field, id_list, indexed_blocks

ROOT = Path(__file__).resolve().parents[1]


def moment(k, rate=Q(2)):
    return Q(factorial(k)) / rate**(k+1)


def integral(poly, endpoint):
    return sum((c*endpoint**(k+1)/(k+1) for k, c in poly.items()), Q())


def multiply(a, b):
    out = Counter()
    for i, x in a.items():
        for j, y in b.items():
            out[i+j] += x*y
    return dict(out)


def boundary_tensor(f, g, endpoint):
    """Limit functional on a tensor, using its two polynomial traces."""
    fm = integral({k+1: c for k, c in f.items()}, endpoint)
    gm = integral({k+1: c for k, c in g.items()}, endpoint)
    return f.get(0, Q())*g.get(0, Q())/4 + Q(3, 4)*(fm*g.get(0, Q())+gm*f.get(0, Q()))


class TripleBoundaryChecks(unittest.TestCase):
    def test_moments_by_antiderivative_and_boundary_value(self):
        for rate in (Q(1, 2), Q(1), Q(2), Q(3)):
            for k in range(7):
                # d[e^(-rate*s) A(s)]/ds = s^k e^(-rate*s).
                anti = {j: -Q(factorial(k), factorial(j))/rate**(k-j+1)
                        for j in range(k+1)}
                derivative = {j: (j+1)*anti.get(j+1, Q())-rate*anti[j]
                              for j in range(k+1)}
                self.assertEqual(derivative, {j: Q(j == k) for j in range(k+1)})
                self.assertEqual(-anti[0], moment(k, rate))
        self.assertEqual(moment(0)**2, Q(1, 4))
        self.assertEqual(moment(0)+moment(1), Q(3, 4))
        self.assertEqual((moment(1)+moment(2))/2, Q(1, 4))

    def test_origin_jacobian_and_first_moments(self):
        for b, c, f0, fx, fy in product((Q(1), Q(4)), (Q(2), Q(3)),
                                       (Q(-2), Q(1)), (Q(0), Q(3)), (Q(-1), Q(2))):
            q = b+c
            direct = q**2*(f0/(4*b*b)+(fx+fy)/(8*b**3))
            changed = q**2/b**2*(f0*moment(0)**2
                         +(fx+fy)*moment(0)*moment(1)/b)
            self.assertEqual(direct, changed)
            self.assertEqual(q**2/b**2, 1+2*c/b+c*c/(b*b))
        # Leading coefficients for a finite polynomial after the substitution.
        for i, j in product(range(4), repeat=2):
            powers = {-(i+j): Q(1), -(i+j+1): Q(4), -(i+j+2): Q(4)}
            constant = powers.get(0, Q())*moment(i)*moment(j)
            self.assertEqual(constant, Q(1, 4) if i == j == 0 else Q())

    def test_axis_substitution_and_trace_coefficient(self):
        for b, xi, s in product((Q(1), Q(7)), (Q(0), Q(1, 3)), (Q(0), Q(2))):
            # Common exp(-2s) is omitted on both sides. d eta=ds/b.
            original = (1+s)*(2*b*xi+s)/(2*b)
            transformed = (1+s)*(xi+s/(2*b))
            self.assertEqual(original, transformed)
        # Affine trace psi(xi,eta)=a+d*eta, at fixed xi.
        for a, d, xi, b in product((Q(-1), Q(2)), (Q(0), Q(3)),
                                   (Q(0), Q(1, 4)), (Q(1), Q(5))):
            poly = multiply({0: Q(1), 1: Q(1)},
                            multiply({0: xi, 1: 1/(2*b)}, {0: a, 1: d/b}))
            actual = sum((c*moment(k) for k, c in poly.items()), Q())
            expected = Q(3, 4)*xi*a + (xi*d+a/2)/(2*b)+Q(5, 16)*d/b**2
            self.assertEqual(actual, expected)

    def test_nineteen_words_and_decay_directions(self):
        directions = ((1, 0), (0, 1), (1, 1))
        counts, dimensions = Counter(), Counter()
        for word in product('PAH', repeat=3):
            if 'H' not in word:
                continue
            p, a, h = (word.count(c) for c in 'PAH')
            counts[p, a, h] += 1
            decay = tuple(sum(directions[i][j] for i, c in enumerate(word) if c != 'P')
                          for j in range(2))
            dimension = sum(v > 0 for v in decay)
            dimensions[p, a, h, dimension] += 1
            if p <= 1:
                self.assertEqual(dimension, 2)
            self.assertLessEqual(Q(p, 2)+a-dimension, 0)
        self.assertEqual(counts, {(2, 0, 1): 3, (1, 1, 1): 6, (0, 2, 1): 3,
                                  (1, 0, 2): 3, (0, 1, 2): 3, (0, 0, 3): 1})
        self.assertEqual(sum(counts.values()), 19)
        self.assertEqual(dimensions[2, 0, 1, 1], 2)
        self.assertEqual(dimensions[2, 0, 1, 2], 1)

    def test_all_component_refinements_and_pole_split(self):
        refined = []
        for word in product('PAH', repeat=3):
            if 'H' not in word:
                continue
            choices = [('arch', 'DS', 'pole', 'trivial') if c == 'H' else (c,)
                       for c in word]
            refined.extend(product(*choices))
        self.assertEqual(len(refined), 208)
        self.assertEqual(len(set(refined)), 208)
        ordinary = [w for w in refined if 'pole' not in w]
        poles = [w for w in refined if 'pole' in w]
        self.assertEqual(len(ordinary), 117)
        self.assertEqual(len(poles), 91)
        # Track the inverse-T degree from every trivial component. At each
        # H slot the no-pole choices have generating polynomial 2+z.
        degrees = Counter(w.count('trivial') for w in ordinary)
        expected = Counter()
        for h, count in ((1, 12), (2, 6), (3, 1)):
            poly = {0: Q(1)}
            for _ in range(h):
                poly = multiply(poly, {0: Q(2), 1: Q(1)})
            for k, coefficient in poly.items():
                expected[k] += count*coefficient
        self.assertEqual(degrees, expected)
        # Every pole factor has x^(1/2)/T^2 <= T^(-3/2) for x<=T.
        for exponent in (Q(0), Q(1, 3), Q(1)):
            self.assertLessEqual(exponent/2-2, Q(-3, 2))

    def test_closed_quadrant_range_and_offdiagonal_exponents(self):
        for kappa in (Q(1, 100), Q(1, 3), Q(9, 10)):
            a = 1-kappa
            for xi, eta in ((Q(0), Q(0)), (a, Q(0)), (Q(0), a), (a/3, 2*a/3)):
                self.assertGreaterEqual(xi, 0)
                self.assertGreaterEqual(eta, 0)
                self.assertLessEqual(xi+eta, a)
                self.assertLessEqual(xi-eta/2, xi+eta)
                self.assertLessEqual(eta-xi/2, xi+eta)
                self.assertLessEqual(-xi/2-2*eta, 0)  # PAA
                self.assertLessEqual(-eta/2-2*xi, 0)  # APA
                self.assertLessEqual(-(xi+eta)/2, 0)  # AAP
                self.assertLessEqual(xi+eta-1, -kappa)
            self.assertLess(a, 1)

    def test_origin_axis_and_interior_functionals_and_exchange(self):
        # Finite polynomial trace models, C^1 when cut off at a. These test
        # the algebraic functional only, not smooth-test admissibility.
        a = Q(1, 4)
        cut = {0: Q(1), 1: -2/a, 2: 1/a**2}
        balanced = multiply(cut, {0: Q(1), 1: -Q(5, 2)/a})
        away_trace = multiply(cut, {2: Q(1)})
        self.assertEqual(integral({k+1: c for k, c in balanced.items()}, a), 0)
        self.assertEqual(boundary_tensor(balanced, balanced, a), Q(1, 4))
        one_axis = Q(3, 4)*integral({k+1: c for k, c in away_trace.items()}, a)
        self.assertGreater(one_axis, 0)
        self.assertEqual(boundary_tensor(away_trace, balanced, a), one_axis)
        self.assertEqual(boundary_tensor(balanced, away_trace, a), one_axis)
        self.assertEqual(boundary_tensor(away_trace, away_trace, a), 0)
        for f, g in product((cut, balanced, away_trace), repeat=2):
            self.assertEqual(boundary_tensor(f, g, a), boundary_tensor(g, f, a))
        # Smooth origin isolation by moment balance uses the same algebra:
        # f=chi*(1-c*x), c=M1/M2, chi(0)=1, M2>0.
        for m1, m2 in ((Q(1, 12), Q(1, 30)), (Q(2, 7), Q(3, 8))):
            self.assertEqual(m1-(m1/m2)*m2, 0)

    def test_axis_phases_full_zero_shifts_and_new_normalization(self):
        zeros = occurrences()
        p, q, c = Q(7), Q(9), Q(2)  # Formal 2pi and logarithms.
        b, L = q-c, (q-c)/p
        for xi, eta in ((Q(0), Q(0)), (Q(1, 3), Q(0)), (Q(0), Q(1, 3))):
            for (d1, g1), (d2, g2), (d3, g3) in zip(zeros, zeros[1:]+zeros[:1], zeros[2:]+zeros[:2]):
                z21, z31 = G(L*(g2-g1), -L*(d2+d1)), G(L*(g3-g1), -L*(d3+d1))
                self.assertEqual(p*I*(xi*z21+eta*z31),
                                 b*(xi*G(d2+d1, g2-g1)+eta*G(d3+d1, g3-g1)))
                t = Q(8)
                D = []
                for d, g in ((d1, g1), (d2, g2), (d3, g3)):
                    z = G(t-g, d)
                    D.append(1+z*z)
                self.assertEqual((2/D[1])*(2/D[2])*(2/D[0]).conjugate()/q,
                                 Q(8)/q/(D[1]*D[2]*D[0].conjugate()))

    def test_claims_links_and_boundary_conventions(self):
        blocks = indexed_blocks((ROOT/'research/theorem-ledger.yaml').read_text())
        claims = {
            'TRIPLE-BOUNDARY-ESTIMATES-001': ('lem:triple-boundary-estimates',
                {'TRIPLE-UNIFORM-001', 'TRIPLE-OFFDIAG-001', 'TRIPLE-RETAINED-001'}),
            'TRIPLE-QUADRANT-LIMIT-001': ('thm:triple-quadrant-limit',
                {'TRIPLE-BOUNDARY-ESTIMATES-001', 'TRIPLE-MASTER-001'})}
        tex = (ROOT/'proofs/triple_explicit_formula.tex').read_text()
        md_path = ROOT/'research/triple-test-functions.md'
        md = md_path.read_text()
        for claim, (label, dependencies) in claims.items():
            block = blocks[claim]
            self.assertEqual(field(block, 'status'), 'proved-draft')
            self.assertEqual(field(block, 'computation_used_in_proof'), 'false')
            self.assertEqual(field(block, 'all_limit_interchanges_justified'), 'true')
            self.assertEqual(set(id_list(field(block, 'dependencies'))), dependencies)
            self.assertIn('UNCONDITIONAL', field(block, 'assumptions'))
            self.assertIn('SUPPORT(relative support in xi>=0, eta>=0, xi+eta<=1-kappa; 0<kappa<1)',
                          field(block, 'assumptions'))
            self.assertIn('label: '+label, block)
            self.assertIn(r'\label{'+label+'}', tex)
            self.assertIn(label, md)
        self.assertIn('generally not Schwartz', md)
        self.assertIn('no additional half weights', md)
        self.assertIn('208', md)
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', md):
            self.assertTrue((md_path.parent/target).is_file(), target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
