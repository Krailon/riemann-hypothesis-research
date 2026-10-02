#!/usr/bin/env python3
"""Exact finite regression checks for the Lemma 3 reconstruction.

Task: verification. Algebra assumptions: UNCONDITIONAL. Finite zero fixtures:
SYNTHETIC_MODEL; the explicitly named specialization checks use RH.
Gaussian rational arithmetic and formal vertical phases only: no floating
point, randomness, zero data, quadrature, or numerical proof certificate.
The analytic proof and positivity argument are in proofs/pair_baseline.tex.
"""

from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction as Q
import unittest


@dataclass(frozen=True)
class G:
    """A Gaussian rational, with exact division."""

    real: Q = Q(0)
    imag: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "real", Q(self.real))
        object.__setattr__(self, "imag", Q(self.imag))

    def __add__(self, other):
        other = other if isinstance(other, G) else G(other)
        return G(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.real, -self.imag)

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, G) else G(other)
        return G(self.real*other.real - self.imag*other.imag,
                 self.real*other.imag + self.imag*other.real)

    __rmul__ = __mul__

    def conjugate(self):
        return G(self.real, -self.imag)

    def __truediv__(self, other):
        other = other if isinstance(other, G) else G(other)
        numerator = self * other.conjugate()
        denominator = other.real**2 + other.imag**2
        return G(numerator.real/denominator, numerator.imag/denominator)

    def __rtruediv__(self, other):
        return G(other) / self


I = G(0, 1)


def weight(z):
    return 4 / (4 - z*z)


def occurrences():
    """Full symmetric synthetic configuration; each tuple is (delta, gamma)."""
    positive = [(Q(-1, 4), Q(3)), (Q(1, 4), Q(3))] * 2
    positive += [(Q(0), Q(5)), (Q(0), Q(7)), (Q(0), Q(7))]
    return positive + [(delta, -gamma) for delta, gamma in positive]


def formal_sum(zeros, base, reflected=False):
    """Coefficients of formal phases X^(i d), for X=base^4.

    Quarter-integral displacements make every amplitude rational. Keeping
    phases formal checks the full reindexing without approximating log(X).
    """
    coefficients = defaultdict(G)
    for delta, gamma in zeros:
        for eta, tau in zeros:
            horizontal = delta + eta if reflected else delta - eta
            exponent = 4*horizontal
            assert exponent.denominator == 1
            d = gamma - tau
            coefficients[d] += base**int(exponent) * weight(G(horizontal, d))
    return dict(coefficients)


class LemmaThreeAlgebra(unittest.TestCase):
    def setUp(self):
        self.zeros = [(delta, gamma) for delta, gamma in occurrences()
                      if 0 < gamma <= 7]

    def test_exact_arithmetic(self):
        # Independent known values guard the tiny arithmetic helper.
        self.assertEqual(I*I, G(-1))
        self.assertEqual(1 / G(1, 1), G(Q(1, 2), Q(-1, 2)))
        self.assertEqual(G(2, 3)*G(4, -1), G(11, 10))

    def test_simple_pole_residues_and_normalization(self):
        for a in (G(1), G(0, Q(1, 2)), G(Q(3, 2), Q(-3, 4)),
                  G(-2, Q(-1, 3))):
            r1 = 1 / (2*I * (1 + (a+I)*(a+I)))
            r2 = 1 / (2*I * (1 + (-a+I)*(-a+I)))
            # Remove pi from the contour integral, then multiply by 2/pi.
            self.assertEqual(2*I*(r1+r2), 2 / (4+a*a))
            self.assertEqual(4*I*(r1+r2), 4 / (4+a*a))

    def test_coincident_pole(self):
        # Residue at i of (u-i)^(-2)(u+i)^(-2).
        residue = -2 / ((2*I)*(2*I)*(2*I))
        self.assertEqual(2*I*residue, G(Q(1, 2)))
        self.assertEqual(4*I*residue, G(1))
        delta, eta, d = Q(1, 4), Q(-1, 4), Q(0)
        self.assertNotEqual(delta, eta)  # Distinct complex zeros, same height.
        self.assertEqual(G(d, -(delta+eta)), G())
        self.assertNotEqual(G(d, -(delta+delta)), G())

    def test_contour_strip_poles(self):
        grid = (Q(-499, 1000), Q(-1, 4), Q(0), Q(1, 4), Q(499, 1000))
        for delta in grid:
            for eta in grid:
                lower, upper = min(0, delta), max(0, delta)
                h = delta + eta
                self.assertLess(abs(h), 1)
                for pole_height in (Q(1), h+1):
                    self.assertGreater(pole_height, upper)
                for pole_height in (Q(-1), h-1):
                    self.assertLess(pole_height, lower)

    def test_shift_substitution_and_denominator(self):
        for delta, gamma in self.zeros:
            for eta, tau in self.zeros:
                z = G(delta+eta, gamma-tau)
                a = G(gamma-tau, -(delta+eta))
                self.assertEqual(a, -I*z)
                self.assertEqual(4+a*a, 4-z*z)
                for t in (Q(-2), Q(0), Q(3, 2), Q(7)):
                    u = G(t-gamma, delta)
                    self.assertEqual(u+a, G(t-tau, -eta))

    def test_fixture_symmetry_multiplicity_and_height_endpoint(self):
        full = Counter(occurrences())
        self.assertEqual(full, Counter((-d, g) for d, g in occurrences()))
        self.assertEqual(full, Counter((d, -g) for d, g in occurrences()))
        self.assertEqual(len(self.zeros), 7)
        self.assertEqual(sum(g == 7 for d, g in self.zeros), 2)
        self.assertEqual(sum(a == b for a in self.zeros for b in self.zeros), 13)
        self.assertEqual(sum(a[1] == b[1] for a in self.zeros for b in self.zeros), 21)

    def test_full_reflection_reindexing(self):
        for base in (Q(1, 2), Q(1), Q(2)):  # X<1, X=1, X>1.
            self.assertEqual(formal_sum(self.zeros, base),
                             formal_sum(self.zeros, base, reflected=True))

    def test_reality_and_inversion(self):
        for base in (Q(1, 2), Q(1), Q(2)):
            original = formal_sum(self.zeros, base)
            conjugate = {-d: value.conjugate() for d, value in original.items()}
            inverse = {-d: value for d, value in formal_sum(self.zeros, 1/base).items()}
            self.assertEqual(original, conjugate)
            self.assertEqual(original, inverse)

    def test_reflection_does_not_preserve_index_diagonal(self):
        reflected = sum((Q(2)**int(8*d)*weight(G(2*d))
                         for d, g in self.zeros), G())
        self.assertNotEqual(reflected, G(len(self.zeros)))

    def test_pair_hermitian_symmetry(self):
        for delta, gamma in self.zeros:
            for eta, tau in self.zeros:
                z = G(delta+eta, gamma-tau)
                swapped = G(eta+delta, tau-gamma)
                self.assertEqual(weight(z).conjugate(), weight(swapped))

    def test_rh_specialization_and_empty_sum(self):
        for d in (Q(-7), Q(0), Q(1, 3), Q(2)):
            self.assertEqual(weight(G(0, d)), G(4/(4+d*d)))
        self.assertEqual(formal_sum([], Q(2)), {})


if __name__ == "__main__":
    unittest.main(verbosity=2)
