#!/usr/bin/env python3
"""Exact algebra checks for PAIR-ASYMPTOTIC-001.

Task: verification. Assumptions: UNCONDITIONAL for the algebra.
Independent rational symbols stand for log T, sqrt(log T), and 2*pi;
they are not numerical evaluations of transcendental constants.
Finite fixtures check normalization and error accounting, not the
analytic estimates or their uniformity. No proof certificate is produced.
Run from the repository root with python3 -B.
"""

from fractions import Fraction as Q
from itertools import product
import unittest


class PairAsymptoticAlgebra(unittest.TestCase):
    def test_main_terms_via_phi_and_c_t(self):
        # Starting from k*Phi = T*q^2/X^2 + T*log X, k denotes 2*pi.
        for t, x, q, log_x, k in (
            (Q(3), Q(1), Q(9, 4), Q(0), Q(7, 3)),
            (Q(16), Q(4), Q(4), Q(2), Q(5)),
            (Q(81), Q(81), Q(9), Q(9), Q(11, 2)),
        ):
            phi = (t*q*q/(x*x) + t*log_x) / k
            c_t = t*q/k
            self.assertEqual(phi/c_t, q/(x*x) + log_x/q)
            # Guards against accidentally normalizing Phi by T*q itself.
            self.assertNotEqual(phi/(t*q), phi/c_t)

    def test_each_error_scale_separately(self):
        # q=s^2 permits exact square-root arithmetic without approximation.
        for t, x, s in (
            (Q(3), Q(1), Q(11, 10)),
            (Q(16), Q(4), Q(2)),
            (Q(81), Q(81), Q(3)),
        ):
            q = s*s
            unnormalized = (t*q/(x*x), t*s, t, x)
            expected = (1/(x*x), 1/s, 1/q, x/(t*q))
            self.assertEqual(tuple(e/(t*q) for e in unnormalized), expected)

    def test_signed_comparison_and_mean_errors(self):
        # R=main+prime_errors and L=k*Phi+comparison_errors, with R=L.
        # Compare exact recovery of Phi against a separately expanded formula.
        t, x, s, k, log_x = Q(16), Q(4), Q(2), Q(7), Q(2)
        q = s*s
        for a, b, c, d in product((Q(-2), Q(0), Q(3)), repeat=4):
            r = t*q*q/(x*x) + t*log_x + a*t*q/(x*x) + b*t*s
            phi = (r - c*t - d*x)/k
            expanded = q/(x*x) + log_x/q + a/(x*x) + b/s - c/q - d*x/(t*q)
            self.assertEqual(phi/(t*q/k), expanded)
            residual = abs(expanded - q/(x*x) - log_x/q)
            self.assertLessEqual(
                residual, abs(a)/(x*x) + (abs(b)+abs(c)+abs(d))/s
            )

    def test_power_substitution_including_closed_endpoints(self):
        # T=b^d and alpha=n/d make X exact. q is a formal log T symbol;
        # log X=alpha*q is imposed by the logarithm identity proved in text.
        for base, degree in ((2, 2), (3, 4), (5, 3)):
            t, q = Q(base**degree), Q(7, 2)
            for n in range(degree + 1):
                alpha, x = Q(n, degree), Q(base**n)
                self.assertEqual(x**degree, t**n)
                self.assertTrue(1 <= x <= t)
                log_x = alpha*q
                self.assertEqual(log_x/q, alpha)
                self.assertEqual(1/(x*x), Q(base)**(-2*n))
                if n == 0:
                    self.assertEqual((q/(x*x), log_x/q, 1/(x*x)), (q, 0, 1))
                if n == degree:
                    self.assertEqual((q/(x*x), log_x/q), (q/(t*t), 1))
                # Negative alpha is represented by its positive-side base.
                self.assertEqual(Q(base)**int(abs(-alpha)*degree), x)

    def test_absorption_preserves_peak_error(self):
        for s in (Q(1), Q(11, 10), Q(2), Q(10), Q(100)):
            q = s*s
            for t in (Q(3), Q(17, 2), Q(100)):
                for x in (Q(1), (1+t)/2, t):
                    self.assertLessEqual(x/(t*q), 1/q)
                    self.assertLessEqual(1/q, 1/s)
            # At X=1 the peak-error scale stays 1 as 1/s decreases.
            self.assertEqual(Q(1)/(1/s), s)
            # Endpoint absorption uses exp(2q)>=2q^2>=q^(3/2).
            self.assertGreaterEqual(2*q*q, q*s)


if __name__ == "__main__":
    unittest.main(verbosity=2)
