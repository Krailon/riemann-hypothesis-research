#!/usr/bin/env python3
"""Finite exact checks: UNCONDITIONAL algebra; SYNTHETIC_MODEL fixtures.

No zero data, floating point, asymptotic verification or proof certificate.
Polynomial tests and rational scales below check finite identities only.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G
from check_pair_rh_audit import field, indexed_blocks
from check_triple_kernel import centers, profile

ROOT = Path(__file__).resolve().parents[1]
SIGNS = tuple(product((-1, 1), repeat=3))
SUBSETS = tuple(s for n in range(4) for s in combinations(range(3), n))


def prod(values):
    result = 1
    for value in values:
        result *= value
    return result


def sign_coefficients(a, d, delta):
    values = {e: profile(centers(a, d, (e[1]*delta[1], e[2]*delta[2],
                                      e[0]*delta[0]))) for e in SIGNS}
    coefficients = {s: sum((prod(e[j] for j in s)*values[e]
                            for e in SIGNS), G())/8 for s in SUBSETS}
    return values, coefficients


class Jet:
    """Exact coefficients through t^2; used only to differentiate fixtures."""
    def __init__(self, c0=0, c1=0, c2=0):
        self.c = tuple(c if isinstance(c, G) else G(c) for c in (c0, c1, c2))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Jet) else Jet(value)

    def __add__(self, other):
        return Jet(*(a+b for a, b in zip(self.c, self.coerce(other).c)))

    __radd__ = __add__

    def __neg__(self):
        return Jet(*(-a for a in self.c))

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __mul__(self, other):
        b = self.coerce(other).c
        return Jet(*(sum((self.c[j]*b[n-j] for j in range(n+1)), G())
                     for n in range(3)))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.coerce(other).c
        out = []
        for n in range(3):
            out.append((self.c[n]-sum((out[j]*b[n-j] for j in range(n)), G()))/b[0])
        return Jet(*out)


def kernel_jet(a, d, delta):
    e1, e2, e3 = delta
    z = (Jet(a, G(0, -e2)), Jet(d, G(0, -e3)), Jet(0, G(0, e1)))
    ds = (z[0]-z[1], z[0]-z[2], z[1]-z[2])
    squares = [v*v for v in ds]
    return (24+sum(squares, Jet())) / prod(4+v for v in squares)


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

    def test_eight_sign_expansion_including_frequency_seams(self):
        for a, d in [(0, 0), (Q(1, 3), Q(-2, 5))]:
            delta = (Q(1, 2), Q(-1, 2), Q(0))
            js, coefficients = sign_coefficients(a, d, delta)
            for xi, eta in [(0, 0), (1, 0), (0, -1), (1, -1), (1, 2)]:
                # b=log 4 is formal, so these half-integral exponents are exact.
                exponents = [2*delta[0]*(xi+eta), 2*delta[1]*xi, 2*delta[2]*eta]
                t = [Q(2)**int(e) for e in exponents]
                ch, sh = [(v+1/v)/2 for v in t], [(v-1/v)/2 for v in t]
                direct = sum((js[e]*(prod(t[j]**e[j] for j in range(3))-1)
                              for e in SIGNS), G())/8
                expanded = coefficients[()]*(prod(ch)-1)
                expanded += sum((coefficients[s]*prod(sh[j] if j in s else ch[j]
                                                       for j in range(3))
                                 for s in SUBSETS if s), G())
                self.assertEqual(direct, expanded)

    def test_sign_coefficients_parity_gap_reflection_and_zero_factors(self):
        for delta in [(Q(1, 2), Q(-1, 3), Q(1, 4)),
                      (Q(0), Q(1, 2), Q(-1, 2))]:
            _, zero = sign_coefficients(0, 0, delta)
            _, forward = sign_coefficients(Q(1, 3), Q(-2, 5), delta)
            _, backward = sign_coefficients(Q(-1, 3), Q(2, 5), delta)
            for s in SUBSETS:
                self.assertEqual(forward[s].conjugate(), (-1)**len(s)*forward[s])
                self.assertEqual(backward[s], (-1)**len(s)*forward[s])
                if len(s) % 2:
                    self.assertEqual(zero[s], G())
                if any(delta[j] == 0 for j in s):
                    self.assertEqual(forward[s], G())

    def test_positive_scalar_sign_average_with_closed_endpoints(self):
        for t, e in product([Q(0), Q(1, 3), Q(-4)], [Q(0), Q(-1, 2), Q(1, 2)]):
            z = G(t, -e)
            direct = (1/(1+z*z)+1/(1+z.conjugate()*z.conjugate()))/2
            expected = (1+t*t-e*e)/((1+t*t-e*e)**2+4*t*t*e*e)
            self.assertEqual(direct, G(expected))
            self.assertGreater(expected, 0)

    def test_independent_reflections_preserve_full_sum_but_not_index_diagonals(self):
        reflection = [1, 0, 3, 2, 4, 6, 5, 8, 7, 9]
        indices = list(product(range(10), repeat=3))
        for signs in SIGNS:
            mapped = [tuple(reflection[i] if signs[j] == -1 else i
                            for j, i in enumerate(ids)) for ids in indices]
            self.assertEqual(Counter(mapped), Counter(indices))
        original = (0, 0, 0)
        reflected = (0, reflection[0], 0)
        self.assertEqual(len(set(original)), 1)
        self.assertEqual(len(set(reflected)), 2)
        self.assertEqual([fixture()[i][1] for i in original],
                         [fixture()[i][1] for i in reflected])

    def test_complete_quadratic_coefficient_by_exact_series_division(self):
        a, d, ell = Q(1, 3), Q(-2, 5), Q(3, 2)
        delta = (Q(1, 5), Q(-1, 4), Q(1, 3))
        u, v = G(ell*a), G(ell*d)
        j0 = profile(centers(a, d, (0, 0, 0)))
        k = [kernel_jet(a, d, tuple(Q(1) if i == j else Q(0)
                                   for i in range(3))).c[1] for j in range(3)]
        observed = G()
        for e in SIGNS:
            ds = tuple(e[j]*delta[j] for j in range(3))
            z1 = Jet(u, G(0, -ell*(ds[0]+ds[1])))
            z2 = Jet(v, G(0, -ell*(ds[0]+ds[2])))
            shifted = 1+z1+z2*G(0, 1)+z1*z1+z1*z2
            observed += (kernel_jet(a, d, ds)*(shifted-polynomial(u, v))).c[2]/8
        fu, fv = 1+2*u+v, G(0, 1)+u
        leading = -j0*ell*ell/2*(4*delta[0]**2+2*delta[1]**2)
        mixing = -G(0, 1)*ell*sum((delta[j]**2*k[j]*df
                                    for j, df in enumerate([fu+fv, fu, fv])), G())
        self.assertEqual(observed, leading+mixing)
        self.assertNotEqual(mixing, G())  # Dropping kernel derivatives fails.

    def test_density_exponents_and_strict_support_threshold(self):
        alpha = Q(331, 4000)
        self.assertEqual(alpha, Q(331, 1000)/4)
        self.assertLess(alpha, Q(1, 8))
        for s in [Q(1, 64), Q(1, 32), alpha-Q(1, 100000)]:
            self.assertLess(-1+8*s, 0)
            self.assertLess(s-alpha, 0)
            self.assertLess(s-1, 0)
            self.assertEqual(2-4*(Q(1, 4)-2*s), 1+8*s)
        self.assertEqual(alpha-alpha, 0)  # Endpoint has no power saving.

    def test_constant_kernel_split_and_normalization_on_degenerate_tuples(self):
        ell, p, b, q, height = Q(3, 2), Q(1), Q(3), Q(5), Q(101)
        c = Q(16)/(3*height*q)
        self.assertEqual(ell, b/(2*p))
        self.assertEqual(c*(3*p/8), 2*p/(height*q))
        for a, d, delta in [(0, 0, (Q(0),)*3),
                            (0, 0, (Q(1, 2), Q(-1, 2), Q(0))),
                            (Q(1, 3), Q(0), (Q(1, 4), Q(0), Q(-1, 2)))]:
            js, coefficients = sign_coefficients(a, d, delta)
            u, v = G(ell*a), G(ell*d)
            differences = {}
            for e in SIGNS:
                z1 = u+G(0, -ell*(e[0]*delta[0]+e[1]*delta[1]))
                z2 = v+G(0, -ell*(e[0]*delta[0]+e[2]*delta[2]))
                differences[e] = polynomial(z1, z2)-polynomial(u, v)
            h = sum(differences.values(), G())/8
            even = c*p*coefficients[()]*h
            constant = 2*p/(height*q)*h
            replacement = c*p*(coefficients[()]-Q(3, 8))*h
            mixing = c*p*sum(((js[e]-coefficients[()])*differences[e]
                              for e in SIGNS), G())/8
            self.assertEqual(even, constant+replacement)
            direct = c*p*sum((js[e]*differences[e] for e in SIGNS), G())/8
            self.assertEqual(direct, constant+replacement+mixing)
            if not any(delta):
                self.assertEqual(direct, G())
            if a == d == 0 and any(delta):
                self.assertNotEqual(coefficients[()], G(Q(3, 8)))

    def test_averaged_kernel_origin_has_no_linear_term_and_exact_quadratic(self):
        # Scale both real gaps and all horizontal parameters by formal t.
        # J/pi = 3/8 - (5/64) sum d_mn^2 + O(t^4).
        for a, d, delta in [(Q(0), Q(0), (Q(0),)*3),
                            (Q(1), Q(-2), (Q(0),)*3),
                            (Q(0), Q(0), (Q(1, 2), Q(-1, 2), Q(0))),
                            (Q(1, 3), Q(2, 5), (Q(1, 7), Q(-1, 4), Q(1, 2)))]:
            average = Jet()
            for e in SIGNS:
                z = (Jet(0, G(a, -e[1]*delta[1])),
                     Jet(0, G(d, -e[2]*delta[2])), Jet(0, G(0, e[0]*delta[0])))
                ds = (z[0]-z[1], z[0]-z[2], z[1]-z[2])
                squares = [v*v for v in ds]
                average += ((24+sum(squares, Jet()))/prod(4+v for v in squares))/8
            self.assertEqual(average.c[0], G(Q(3, 8)))
            self.assertEqual(average.c[1], G())
            self.assertEqual(average.c[2], G(Q(5, 32)*
                             (sum(v*v for v in delta)-a*a+a*d-d*d)))

    def test_kernel_free_reindexing_with_independent_cutoffs_and_multiplicity(self):
        zeros, ell = fixture(), Q(3, 2)
        for anchor_cut, second_cut, third_cut in [(3, 3, 5), (5, 5, 3)]:
            slot1 = [z for z in zeros if 0 < z[1] <= anchor_cut]
            slot2 = [z for z in zeros if abs(z[1]) <= second_cut]
            slot3 = [z for z in zeros if abs(z[1]) <= third_cut]
            direct, averaged = G(), G()
            for (e1, g1), (e2, g2), (e3, g3) in product(slot1, slot2, slot3):
                u, v = G(ell*(g2-g1)), G(ell*(g3-g1))
                w = Q(1) if g1 == 3 else Q(3, 2)
                direct += w*(polynomial(u+G(0, -ell*(e1+e2)),
                                        v+G(0, -ell*(e1+e3)))-polynomial(u, v))
                for s1, s2, s3 in SIGNS:
                    z1, z2 = u+G(0, -ell*(s1*e1+s2*e2)), v+G(0, -ell*(s1*e1+s3*e3))
                    averaged += w*(polynomial(z1, z2)-polynomial(u, v))/8
            self.assertEqual(direct, averaged)
            self.assertNotEqual(direct, G())  # Symmetry does not prove vanishing.


if __name__ == '__main__':
    unittest.main()
