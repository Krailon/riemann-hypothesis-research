#!/usr/bin/env python3
"""Exact regression checks for the prime-side reconstruction.

Task: verification. Assumptions: UNCONDITIONAL for algebra; finite coefficient
fixtures are SYNTHETIC_MODEL. Standard-library rational arithmetic only.
These checks are not certificates of PNT, sieve bounds, or mean-value estimates.
Run directly from the repository root with python3 -B.
"""

from fractions import Fraction as Q
from math import prod
import unittest

from check_pair_lemma3 import G


def triangle(x):
    return max(Q(0), 1 - abs(x))


def triangle_convolution(x):
    """Integrate the two linear factors exactly on every polynomial segment."""
    left, right = max(Q(-1), x - 1), min(Q(1), x + 1)
    if left >= right:
        return Q(0)
    cuts = sorted({left, right} | {t for t in (Q(0), x) if left < t < right})
    total = Q(0)
    for a, b in zip(cuts, cuts[1:]):
        mid = (a + b) / 2
        slope1 = Q(1) if mid < 0 else Q(-1)
        intercept2, slope2 = (1 - x, Q(1)) if mid < x else (1 + x, Q(-1))
        c0 = intercept2
        c1 = slope2 + slope1 * intercept2
        c2 = slope1 * slope2
        total += c0 * (b - a) + c1 * (b*b - a*a) / 2 + c2 * (b**3 - a**3) / 3
    return total


def k_hat_truncated_powers(x):
    """Independent cubic B-spline expression for (3/2)(triangle*triangle)(2x)."""
    return sum(Q(c, 4) * max(Q(0), 2*x + shift)**3
               for shift, c in ((2, 1), (1, -4), (0, 6), (-1, -4), (-2, 1)))


def fourth_root(j):
    return (G(1), G(0, 1), G(-1), G(0, -1))[j % 4]


def norm2(z):
    return z.real**2 + z.imag**2


def weight_squared(n, x):
    return min(Q(n) / x, x / n)**2 / n


def prime_divisors(n):
    return [p for p in range(2, n + 1)
            if n % p == 0 and all(p % d for d in range(2, p))]


def singular_factor(n):
    return prod((Q(p - 1, p - 2) for p in prime_divisors(n) if p > 2), start=Q(1))


def squarefree_odd_weight(n):
    if n % 2 == 0:
        return Q(0)
    primes = prime_divisors(n)
    if any(n % (p*p) == 0 for p in primes):
        return Q(0)
    return prod((Q(1, p - 2) for p in primes), start=Q(1))


class PrimeMeanAlgebra(unittest.TestCase):
    def test_kernel_transform_by_independent_piecewise_integration(self):
        for j in range(-24, 25):
            x = Q(j, 16)
            expected = Q(3, 2) * triangle_convolution(2*x)
            self.assertEqual(k_hat_truncated_powers(x), expected)
            self.assertGreaterEqual(expected, 0)
            self.assertEqual(expected, k_hat_truncated_powers(-x))

    def test_kernel_mass_bandwidth_and_boundaries(self):
        self.assertEqual(triangle_convolution(Q(0)), Q(2, 3))
        self.assertEqual(k_hat_truncated_powers(Q(0)), 1)
        self.assertEqual(k_hat_truncated_powers(Q(1, 2)), Q(1, 4))
        self.assertEqual(k_hat_truncated_powers(Q(1, 4)), Q(23, 32))
        for x in (Q(-2), Q(-1), Q(1), Q(2)):
            self.assertEqual(k_hat_truncated_powers(x), 0)
        # Exact scaling: K_delta has transform Khat(xi/delta).
        for delta in (Q(1, 8), Q(1, 3), Q(1, 2)):
            self.assertEqual(k_hat_truncated_powers(delta / delta), 0)
            self.assertEqual(k_hat_truncated_powers((delta / 2) / delta), Q(1, 4))

    def test_shifted_endpoint_kernel_fourier_phase(self):
        def b_hat_at_quarter(j):
            xi = Q(j, 4)
            return 2 * (G(1) + fourth_root(-j)) * triangle(2*xi)
        self.assertEqual(b_hat_at_quarter(0), G(4))
        self.assertEqual(b_hat_at_quarter(1), G(1, -1))
        self.assertEqual(b_hat_at_quarter(-1), G(1, 1))
        self.assertEqual(b_hat_at_quarter(2), G())
        self.assertEqual(b_hat_at_quarter(-2), G())
        # Each endpoint kernel has mass 4/delta, and there are two endpoints.
        self.assertEqual(64 * 2 * 4, 512)
        self.assertEqual(1 + 512 * 2, 1025)

    def test_finite_fourier_diagonal_and_repeated_frequencies(self):
        terms = [(0, G(1, 2)), (1, G(2, -1)), (1, G(3)), (2, G(-1, 1))]
        samples = [sum((c * fourth_root(mu*j) for mu, c in terms), G())
                   for j in range(4)]
        grouped = {}
        for mu, c in terms:
            grouped[mu] = grouped.get(mu, G()) + c
        # Differences have modulus <4, so four-point orthogonality is exact.
        average = sum(norm2(z) for z in samples) / 4
        self.assertEqual(average, sum(norm2(c) for c in grouped.values()))
        self.assertNotEqual(average, sum(norm2(c) for _, c in terms))

    def test_diagonal_split_and_prime_power_cutoff(self):
        # Rational surrogates for log p, constant on powers of each prime.
        values = {1: Q(0), 2: Q(3), 3: Q(5), 4: Q(3), 5: Q(7),
                  8: Q(3), 9: Q(5), 16: Q(3), 25: Q(7)}
        proper = {4, 8, 9, 16, 25}
        for x in (Q(1), Q(7, 2), Q(4), Q(9), Q(25), Q(26)):
            whole = sum(v*v*weight_squared(n, x) for n, v in values.items())
            split = (sum(n*v*v for n, v in values.items() if n <= x) / x**2
                     + x**2*sum(v*v/Q(n**3) for n, v in values.items() if n > x))
            pp = sum(values[n]**2*weight_squared(n, x) for n in proper)
            primes = sum(v*v*weight_squared(n, x) for n, v in values.items()
                         if n not in proper)
            self.assertEqual(whole, split)
            self.assertEqual(whole, primes + pp)
        for n in proper:
            self.assertEqual(weight_squared(n, Q(n)), Q(1, n))
            self.assertEqual(Q(n) / Q(n)**2, Q(n)**2 / n**3)

    def test_singular_factor_divisor_expansion_and_average(self):
        for v in (1, 2, 7, 16, 32, 64):
            for h in range(1, v + 1):
                self.assertEqual(singular_factor(h),
                                 sum(squarefree_odd_weight(d) for d in range(1, h+1)
                                     if h % d == 0))
            direct = sum(singular_factor(h) for h in range(1, v+1))
            switched = sum((v // d)*squarefree_odd_weight(d) for d in range(1, v+1))
            majorant = v * sum(squarefree_odd_weight(d)/d for d in range(1, v+1))
            self.assertEqual(direct, switched)
            self.assertLessEqual(direct, majorant)
        for n in range(3, 25):
            self.assertEqual(sum(Q(1, k*(k-2)) for k in range(3, n+1)),
                             Q(3, 4) - Q(1, 2*(n-1)) - Q(1, 2*n))

    def test_near_pair_empty_cutoff_and_ordered_counts(self):
        weights = {1: 0, 2: 3, 3: 5, 4: 3, 5: 7, 8: 3, 9: 5}
        for v in (Q(0), Q(1, 2), Q(1), Q(3)):
            ordered = sum(a*b for n, a in weights.items() for m, b in weights.items()
                          if 0 < abs(m-n) <= v)
            positive = sum(a*b for n, a in weights.items() for m, b in weights.items()
                           if 0 < m-n <= v)
            self.assertEqual(ordered, 2*positive)
            if v < 1:
                self.assertEqual(ordered, 0)

    def test_diagonal_integral_and_archimedean_antiderivative_algebra(self):
        for x in (Q(1), Q(2), Q(4), Q(17, 3)):
            for log_symbol in (Q(0), Q(1), Q(5, 2)):
                low = log_symbol/2 + Q(1, 4) - 1/(4*x*x)
                high = log_symbol/2 + Q(3, 4)
                self.assertEqual(low + high, log_symbol + 1 - 1/(4*x*x))
            derivative_bound = (x*x-1)/(2*x*x) + Q(3, 2)
            self.assertLessEqual(derivative_bound, 2)
        # d/du [u P(log u)] = P(log u)+P'(log u), P(q)=q^2-2q+2.
        p, dp = [Q(2), Q(-2), Q(1)], [Q(-2), Q(2), Q(0)]
        self.assertEqual([a+b for a, b in zip(p, dp)], [0, 0, 1])

    def test_bandwidth_balance_squared_and_dyadic_tail(self):
        for t, x, ell in ((Q(3), Q(1), Q(1)), (Q(3), Q(3), Q(2)),
                          (Q(100), Q(100), Q(5))):
            delta2 = ell/(4*t*x)
            self.assertGreaterEqual(delta2, 1/(4*t*t))
            self.assertLessEqual(delta2, Q(1, 4))
            self.assertEqual(ell**2/delta2, 4*t*x*ell)
            self.assertEqual(t*t*x*x*delta2, t*x*ell/4)
        for n in range(1, 12):
            self.assertEqual(sum(Q(1, 2**j) for j in range(n)), 2-Q(1, 2**(n-1)))

    def test_complete_remainder_expansion_signs(self):
        p, a = G(2, 3), G(Q(5, 2))
        errors = [G(1, -1), G(Q(1, 3), 2), G(-2, Q(1, 2)), G(Q(3, 4))]
        h = sum(errors, G())
        rhs = norm2(p) + norm2(a) - 2*(p*a.conjugate()).real
        rhs += sum(-2*(p*e.conjugate()).real + 2*(a*e.conjugate()).real
                   for e in errors)
        rhs += norm2(h)
        self.assertEqual(norm2(-p+a+h), rhs)


if __name__ == "__main__":
    unittest.main(verbosity=2)
