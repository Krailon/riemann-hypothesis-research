#!/usr/bin/env python3
"""Exact checks for the rational kernel, localization bookkeeping and limits.

Task: verification. Assumptions: UNCONDITIONAL for finite algebra;
SYNTHETIC_MODEL for inherited quartet-symmetric zero fixtures. Constants
pi, logarithms and scales are formal when replaced by rational fixtures.
No numerical integration, asymptotic proof or numerical certificate.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G, I, occurrences
from check_pair_rh_audit import field, id_list, indexed_blocks

ROOT = Path(__file__).resolve().parents[1]


def add(*polys):
    out = defaultdict(G)
    for poly in polys:
        for monomial, value in poly.items():
            out[monomial] += value
    return {k: v for k, v in out.items() if v != G()}


def scale(poly, value):
    return {k: value*v for k, v in poly.items() if value*v != G()}


def multiply(*polys):
    out = {(0, 0): G(1)}
    for poly in polys:
        nxt = defaultdict(G)
        for (a, b), v in out.items():
            for (c, d), w in poly.items():
                nxt[a+c, b+d] += v*w
        out = {k: v for k, v in nxt.items() if v != G()}
    return out


ONE = {(0, 0): G(1)}
A = {(1, 0): G(1)}
B = {(0, 1): G(1)}


def centers(a, b, deltas):
    dj, dk, dl = deltas
    return (G(a, -dj), G(b, -dk), G(0, dl))


def profile(z):
    """J/pi, exactly; includes collisions."""
    ds = (z[0]-z[1], z[0]-z[2], z[1]-z[2])
    numerator = 24+sum((d*d for d in ds), G())
    denominator = G(1)
    for d in ds:
        denominator *= 4+d*d
    return numerator/denominator


def residue_sum(z):
    total = G()
    for j in range(3):
        term = G(1)
        for k in range(3):
            if j != k:
                d = z[j]-z[k]
                term /= d*(d+2*I)
        total += term
    return total


def profile_polynomials(deltas):
    dj, dk, dl = deltas
    ds = (add(A, scale(B, -1), scale(ONE, G(0, -dj+dk))),
          add(A, scale(ONE, G(0, -dj-dl))),
          add(B, scale(ONE, G(0, -dk-dl))))
    squared = [multiply(d, d) for d in ds]
    numerator = add(scale(ONE, 24), *squared)
    denominator = multiply(*(add(scale(ONE, 4), p) for p in squared))
    return numerator, denominator


class TripleKernelChecks(unittest.TestCase):
    def test_residue_cancellation_as_exact_polynomial_identity(self):
        pairs = [((0, 1), add(A, scale(B, -1))), ((0, 2), A), ((1, 2), B)]
        terms = []
        for j in range(3):
            factors = []
            for (i, k), d in pairs:
                if j == i:
                    factors.append(multiply(d, add(d, scale(ONE, -2*I))))
                elif j == k:
                    factors.append(multiply(d, add(d, scale(ONE, 2*I))))
                else:
                    factors.append(multiply(d, d, add(multiply(d, d), scale(ONE, 4))))
            terms.append(multiply(*factors))
        expected = multiply(add(scale(ONE, 24), *(multiply(d, d) for _, d in pairs)),
                            *(multiply(d, d) for _, d in pairs))
        self.assertEqual(add(*terms), expected)
        self.assertTrue(all(v.imag == 0 for v in expected.values()))

    def test_generic_residues_against_closed_form(self):
        for a, b in ((Q(1), Q(3)), (Q(-2), Q(1, 3)), (Q(1, 7), Q(2))):
            for deltas in ((Q(1, 4), Q(-1, 3), Q(1, 5)),
                           (Q(-1, 2), Q(0), Q(1, 2))):
                z = centers(a, b, deltas)
                self.assertEqual(len(set(z)), 3)
                self.assertEqual(residue_sum(z), profile(z))

    def test_collisions_horizontal_endpoints_and_denominator_gap(self):
        for d in (Q(-1, 2), Q(-1, 4), Q(0), Q(1, 2)):
            self.assertEqual(profile(centers(0, 0, (d, d, -d))), G(Q(3, 8)))
        for a, b in product((Q(-2), Q(0), Q(3, 2)), repeat=2):
            for deltas in product((Q(-1, 2), Q(0), Q(1, 2)), repeat=3):
                z = centers(a, b, deltas)
                for j, k in ((0, 1), (0, 2), (1, 2)):
                    d = z[j]-z[k]
                    denominator = 4+d*d
                    self.assertGreaterEqual(denominator.real, 3+d.real*d.real)
                profile(z)  # Exact division must remain defined.
        for b in (Q(-2), Q(0), Q(1, 3)):
            actual = profile(centers(0, b, (Q(0),)*3))
            self.assertEqual(actual, G((24+2*b*b)/(4*(4+b*b)**2)))

    def test_symmetries_and_repeated_full_zero_tuples(self):
        zeros = occurrences()
        self.assertLess(len(set(zeros)), len(zeros))
        for j, k, anchor in ((0, 0, 0), (0, 2, 0), (1, 5, 8), (6, 3, 11)):
            dj, gj = zeros[j]; dk, gk = zeros[k]; dl, gl = zeros[anchor]
            a, b = gj-gl, gk-gl
            value = profile(centers(a, b, (dj, dk, dl)))
            self.assertEqual(value, profile(centers(b, a, (dk, dj, dl))))
            self.assertEqual(value.conjugate(), profile(centers(a, b, (-dj, -dk, -dl))))
            t = Q(7, 2); v = t-gl
            original = []
            for delta, gamma, sign in ((dj, gj, 1), (dk, gk, 1), (dl, gl, -1)):
                w = G(t-gamma, sign*delta)
                original.append(1+w*w)
            transformed = [1+(G(v)-z)*(G(v)-z) for z in centers(a, b, (dj, dk, dl))]
            self.assertEqual(original, transformed)

    def test_two_factor_integral_and_tuplewise_constant(self):
        for d in (Q(-3), Q(-1, 2), Q(1, 3), Q(2)):
            residues = 1/(d*(G(d)+2*I))+1/(d*(G(d)-2*I))
            self.assertEqual(residues, G(2/(4+d*d)))
        self.assertEqual(Q(2, 4), Q(1, 2))  # Coincident pair convolution / pi.
        self.assertEqual(Q(4, 3)**3, Q(64, 27))
        for v in (Q(-3), Q(-1), Q(0), Q(1, 2), Q(1), Q(4)):
            self.assertLessEqual(abs(v)/(1+v*v), Q(1, 2))
        for d in (Q(0), Q(1, 2), Q(3)):
            coefficient = Q(64, 27)*Q(1, 2)*2/(4+d*d)
            self.assertEqual(coefficient, Q(64, 27)/(4+d*d))
            self.assertLessEqual(coefficient, Q(16, 27))

    def test_disjoint_error_regions_and_endpoint_priority(self):
        def omega(t, T):
            x = t/T
            return (x-1)**2*(2-x)**2 if 1 <= x <= 2 else Q()
        for T in (Q(3), Q(5)):
            grid = (Q(-2), Q(0), T, Q(3, 2)*T, 2*T, 3*T, 4*T)
            for t, g in product(grid, repeat=2):
                near = abs(t-g) <= T
                center = abs(t-g) > T and T <= t <= 2*T
                anchor = abs(t-g) > T and not T <= t <= 2*T and T <= g <= 2*T
                self.assertLessEqual(sum((near, center, anchor)), 1)
                difference = omega(t, T)-omega(g, T)
                self.assertEqual(sum((Q(flag)*difference for flag in (near, center, anchor)), Q()),
                                 difference)
                if near and difference:
                    self.assertTrue(0 <= t <= 3*T)
                if abs(t-g) == T:
                    self.assertTrue(near)
                    self.assertFalse(center or anchor)
                if anchor:
                    self.assertEqual(difference, -omega(g, T))

    def test_dyadic_tail_moments(self):
        for n in range(12):
            sums = [sum((Q(m**k, 2**m) for m in range(n+1)), Q()) for k in range(3)]
            self.assertEqual(sums[0], 2-Q(1, 2**n))
            self.assertEqual(sums[1], 2-Q(n+2, 2**n))
            self.assertEqual(sums[2], 6-Q(n*n+4*n+6, 2**n))
        for L in (Q(1), Q(3), Q(10)):
            self.assertLessEqual(2*L+2, 4*L)
            self.assertLessEqual(2*L*L+4*L+6, 12*L*L)

    def test_zero_gap_horizontal_profile_and_nonconstant_example(self):
        for ds in product((Q(-1, 2), Q(-1, 4), Q(0), Q(1, 2)), repeat=3):
            dj, dk, dl = ds
            hs = (dj-dk, dj+dl, dk+dl)
            denominator = Q(1)
            for h in hs:
                denominator *= 4-h*h
            value = (24-sum(h*h for h in hs))/denominator
            self.assertEqual(profile(centers(0, 0, ds)), G(value))
        d = Q(1, 4)
        self.assertEqual(profile(centers(0, 0, (d, d, d))), G(Q(94, 225)))
        self.assertNotEqual(Q(94, 225), Q(3, 8))

    def test_critical_formula_and_microscopic_taylor_coefficients(self):
        for a, b in product((Q(-2), Q(0), Q(1, 3)), repeat=2):
            expected = (24+a*a+b*b+(a-b)**2)/((4+a*a)*(4+b*b)*(4+(a-b)**2))
            self.assertEqual(profile(centers(a, b, (Q(0),)*3)), G(expected))
        numerator, denominator = profile_polynomials((Q(0),)*3)
        quadratic = add(multiply(A, A), multiply(B, B), scale(multiply(A, B), -1))
        approximation = add(scale(ONE, Q(3, 8)), scale(quadratic, Q(-5, 32)))
        residual = add(numerator, scale(multiply(denominator, approximation), -1))
        self.assertTrue(residual)
        self.assertTrue(all(i+j >= 4 for i, j in residual))
        self.assertTrue(all((i+j) % 2 == 0 for i, j in numerator))
        self.assertTrue(all((i+j) % 2 == 0 for i, j in denominator))
        # General horizontal parameters can have a nonzero linear gap term.
        n, d = profile_polynomials((Q(1, 4),)*3)
        n0, d0 = n[0, 0], d[0, 0]
        derivative_a = (n.get((1, 0), G())*d0-n0*d.get((1, 0), G()))/(d0*d0)
        self.assertNotEqual(derivative_a, G())
        self.assertEqual(derivative_a.real, 0)

    def test_normalization_and_support_transfer(self):
        for T, q, c, p in ((Q(10), Q(7), Q(2), Q(6)), (Q(20), Q(11), Q(3), Q(7))):
            # p stands for 2*pi; q,c stand for log T,log(2*pi).
            b, LT = q-c, (q-c)/p
            original = 8/(T*q)*(3*p/16)
            standard = (3*b/(2*q))/(T*LT)
            self.assertEqual(original, standard)
            for kappa in (Q(1, 10), Q(1, 2), Q(9, 10)):
                self.assertEqual((1-kappa)*b-q, -kappa*b-c)
            self.assertEqual(8/q*(Q(3, 8)/T), 8/(T*q)*Q(3, 8))

    def test_claims_labels_links_and_assumption_separation(self):
        blocks = indexed_blocks((ROOT/'research/theorem-ledger.yaml').read_text())
        claims = {
            'TRIPLE-KERNEL-PROFILE-001': ('lem:triple-kernel-profile', {'TRIPLE-MASTER-001'}),
            'TRIPLE-KERNEL-LOCALIZATION-001': ('lem:triple-kernel-localization',
                {'TRIPLE-KERNEL-PROFILE-001', 'TRIPLE-MASTER-001', 'PAIR-COUNT-001',
                 'PAIR-COUNT-KERNEL-001', 'TRIPLE-SIGNED-SECTORS-001', 'TRIPLE-SIGNED-TEST-FUNCTION-001'}),
            'TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001': ('cor:triple-kernel-critical',
                {'TRIPLE-KERNEL-PROFILE-001', 'TRIPLE-KERNEL-LOCALIZATION-001'})}
        tex = (ROOT/'proofs/triple_explicit_formula.tex').read_text()
        md_path = ROOT/'research/triple-kernel.md'
        md = md_path.read_text()
        for claim, (label, dependencies) in claims.items():
            block = blocks[claim]
            self.assertEqual(field(block, 'status'), 'proved-draft')
            self.assertEqual(field(block, 'computation_used_in_proof'), 'false')
            self.assertEqual(field(block, 'all_limit_interchanges_justified'), 'true')
            self.assertEqual(set(id_list(field(block, 'dependencies'))), dependencies)
            self.assertIn('UNCONDITIONAL', field(block, 'assumptions'))
            self.assertIn('label: '+label, block)
            self.assertIn(r'\label{'+label+'}', tex)
            self.assertIn(label, md)
        self.assertIn('correlation consequence only', field(blocks['TRIPLE-KERNEL-LOCALIZATION-001'], 'assumptions'))
        self.assertEqual(field(blocks['TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001'], 'assumptions'),
                         '[UNCONDITIONAL]')
        self.assertIn('conditional interpretation only', md)
        self.assertIn('does not impose RH', tex)
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', md):
            self.assertTrue((md_path.parent/target).is_file(), target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
