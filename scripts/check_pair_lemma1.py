#!/usr/bin/env python3
"""Exact finite regression checks for the Lemma 1 reconstruction.

Task: verification. Assumptions: UNCONDITIONAL.
Uses only standard-library rational arithmetic; no floating point, randomness,
zero dataset, or numerical proof certificate. These checks catch algebra and
endpoint regressions; the analytic proof is in proofs/pair_baseline.tex.
Run from any directory with: python3 /path/to/scripts/check_pair_lemma1.py
"""

from fractions import Fraction as Q
import unittest


def kernel(y):
    """The exact piecewise Mellin-kernel value, including y=1."""
    return y - 1 / y if y > 1 else Q(0)


class LemmaOneAlgebra(unittest.TestCase):
    def test_paired_resolvents(self):
        # These are exact substitutions in the rational identity, not a
        # substitute for the common-denominator proof in the manuscript.
        for r in (Q(-3), Q(-1, 2), Q(0), Q(1, 3), Q(3, 2), Q(5)):
            with self.subTest(r=r):
                self.assertEqual(1 / (1 - r) - 1 / (-1 - r), 2 / (1 - r*r))

    def test_pole_residue_sign(self):
        # After removing the common X^(1-s), the contour residue is -E_pole.
        for s in (Q(1, 4), Q(1, 2), Q(3, 4), Q(3, 2)):
            with self.subTest(s=s):
                self.assertEqual(2 / ((1 - s)**2 - 1), -2 / (s * (2 - s)))

    def test_trivial_zero_pairing(self):
        for m in range(1, 8):
            for s in (Q(1, 4), Q(1, 2), Q(3, 4)):
                with self.subTest(m=m, s=s):
                    a = 2*m + s
                    self.assertEqual(1 / (a - 1) - 1 / (a + 1), 2 / (a*a - 1))

    def test_prime_series_recombination(self):
        # Factor out Lambda(n)n^(-s); retain the complete Euler-series term.
        for x in (Q(1), Q(3, 2), Q(2), Q(4), Q(9), Q(17, 2)):
            for n in range(1, 13):
                with self.subTest(x=x, n=n):
                    self.assertEqual(kernel(x / n) - x / n, -min(Q(n) / x, x / n))

    def test_prime_power_endpoints(self):
        # The common cutoff convention disappears because the paired
        # coefficient is zero. Test one-sided neighboring rational X too.
        for n in (2, 3, 4, 8, 9, 25):
            x = Q(n)
            for theta in (Q(0), Q(1, 2), Q(1)):
                self.assertEqual(theta * (x / n - n / x) - x / n, -1)
            for epsilon in (Q(1, 10), Q(1, 1000)):
                left = -min(Q(n)/(x-epsilon), (x-epsilon)/n)
                right = -min(Q(n)/(x+epsilon), (x+epsilon)/n)
                self.assertEqual(left, -(x-epsilon)/n)
                self.assertEqual(right, -Q(n)/(x+epsilon))

    def test_x_equals_one(self):
        self.assertEqual(kernel(Q(1)), 0)
        for n in range(2, 15):
            self.assertEqual(kernel(Q(1, n)) - Q(1, n), -Q(1, n))

    def test_zero_denominator_and_rh_specialization(self):
        for delta in (Q(-1, 2), Q(-1, 3), Q(0), Q(1, 3), Q(1, 2)):
            for v in (Q(-10), Q(-1), Q(0), Q(1, 7), Q(2)):
                real = 1 + v*v - delta*delta
                imag = 2*v*delta
                self.assertGreaterEqual(real, Q(3, 4) * (1 + v*v))
                self.assertGreater(real*real + imag*imag, 0)
                self.assertEqual(2*v*(-delta), -imag)
                if delta == 0:
                    self.assertEqual(real, 1 + v*v)
                    self.assertEqual(imag, 0)

    def test_modulus_majorants(self):
        for t in (Q(-100), Q(-1), Q(0), Q(1, 5), Q(3)):
            pole_squared = (t*t + Q(1, 4)) * (t*t + Q(9, 4))
            self.assertGreaterEqual(pole_squared, (1 + t*t)**2 / 4)
            for m in range(1, 8):
                trivial_squared = ((2*m-Q(1, 2))**2+t*t) * ((2*m+Q(3, 2))**2+t*t)
                self.assertGreaterEqual(trivial_squared, (m*m + t*t)**2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
