#!/usr/bin/env python3
"""Exact finite regression checks for the Lemmas 2/4 reconstruction.

Task: verification. Algebra assumptions: UNCONDITIONAL. Finite zero fixtures:
SYNTHETIC_MODEL. The named RH specialization is only a separate algebra check.
Standard-library rational arithmetic; no random inputs, zeta data, numerical
quadrature, or analytic proof certificate. Run directly with python3.
"""

from collections import Counter
from fractions import Fraction as Q
import unittest

from check_pair_lemma3 import G


def norm_squared(value):
    return value.real**2 + value.imag**2


def zeros():
    """Full reflection/conjugation symmetry, retaining occurrence duplicates."""
    positive = [(Q(0), Q(2))]
    positive += [(Q(-1, 4), Q(3)), (Q(1, 4), Q(3))] * 2
    positive += [(Q(-1, 4), Q(6)), (Q(1, 4), Q(6))]
    positive += [(Q(0), Q(7))] * 2
    return positive + [(delta, -gamma) for delta, gamma in positive]


def inclusive_count(configuration, height):
    return sum(0 < gamma <= height for delta, gamma in configuration)


def midpoint_count(configuration, height):
    return sum((Q(1) if 0 < gamma < height else
                Q(1, 2) if gamma == height else Q(0))
               for delta, gamma in configuration)


def envelope(configuration):
    return max([Q(0)] + [delta for delta, gamma in configuration])


def value_at_x_one(configuration, t):
    """Actual finite v-sum at X=1, where every vertical phase equals one."""
    total = G()
    for delta, gamma in configuration:
        u = G(t-gamma, delta)
        total += 1 / (1+u*u)
    return total


class LemmaFourAlgebra(unittest.TestCase):
    def setUp(self):
        self.full = zeros()
        self.t_height, self.z_height = Q(3), Q(6)
        self.retained = [(d, g) for d, g in self.full if abs(g) <= self.z_height]
        self.interior = [(d, g) for d, g in self.full if 0 < g <= self.t_height]

    def test_fixture_symmetry_and_cutoff_partition(self):
        self.assertEqual(Counter(self.full), Counter((-d, g) for d, g in self.full))
        self.assertEqual(Counter(self.full), Counter((d, -g) for d, g in self.full))
        far = [(d, g) for d, g in self.full if abs(g) > self.z_height]
        exterior = [(d, g) for d, g in self.retained
                    if g <= 0 or g > self.t_height]
        self.assertEqual(Counter(self.full), Counter(self.retained) + Counter(far))
        self.assertEqual(Counter(self.retained), Counter(self.interior) + Counter(exterior))
        self.assertEqual(sum(g == 3 for d, g in self.interior), 4)
        self.assertEqual(sum(g == 6 for d, g in self.retained), 2)
        self.assertEqual(sum(g == -6 for d, g in self.retained), 2)
        self.assertFalse(any(abs(g) == 6 for d, g in far))
        self.assertEqual(len(self.interior), 5)  # A set would lose multiplicity.

    def test_midpoint_to_inclusive_and_padded_interval(self):
        self.assertEqual(inclusive_count(self.full, Q(3)), 5)
        self.assertEqual(midpoint_count(self.full, Q(3)), Q(3))
        for v in (Q(2), Q(5, 2), Q(3), Q(5), Q(6), Q(7), Q(8)):
            self.assertLessEqual(midpoint_count(self.full, v-1),
                                 inclusive_count(self.full, v))
            self.assertLessEqual(inclusive_count(self.full, v),
                                 midpoint_count(self.full, v+1))
            closed_interval = sum(v <= g <= v+1 for d, g in self.full)
            self.assertLessEqual(closed_interval, midpoint_count(self.full, v+2)
                                 - midpoint_count(self.full, v-1))

    def test_difference_of_squares_includes_quadratic_remainder(self):
        for a in (G(), G(3, 4), G(-2, Q(1, 3))):
            for r in (G(), G(1), G(Q(-1, 4), 2)):
                difference = norm_squared(a) - norm_squared(a-r)
                self.assertEqual(difference,
                                 2*(a*r.conjugate()).real - norm_squared(r))
        # A zero full sum does not force its finite truncation to vanish.
        self.assertEqual(norm_squared(G()) - norm_squared(G()-G(1)), -1)

    def test_finite_signed_error_decomposition(self):
        # A finite weighted analogue checks telescoping signs, not quadrature.
        inside = [(Q(0), Q(1, 3)), (Q(1), Q(2)), (Q(3), Q(1, 2))]
        outside = [(Q(-2), Q(1)), (Q(4), Q(3, 2)), (Q(8), Q(1, 5))]

        def mass(configuration, samples):
            return sum(w*norm_squared(value_at_x_one(configuration, t))
                       for t, w in samples)

        lhs = 4*mass(self.full, inside)
        norm_term = 4*mass(self.interior, inside+outside)
        e_trunc = 4*(mass(self.full, inside)-mass(self.retained, inside))
        e_height = 4*(mass(self.retained, inside)-mass(self.interior, inside))
        e_extension = -4*mass(self.interior, outside)
        self.assertEqual(lhs, norm_term+e_trunc+e_height+e_extension)
        self.assertLess(e_extension, 0)

    def test_phase_removal_and_normalization(self):
        for t in (Q(0), Q(3, 2), Q(3)):
            u = value_at_x_one(self.full, t)
            for unit in (G(1), G(0, 1), G(Q(3, 5), Q(4, 5))):
                self.assertEqual(norm_squared(unit), 1)
                self.assertEqual(norm_squared(2*unit*u), 4*norm_squared(u))

    def test_horizontal_envelope_and_empty_case(self):
        b = envelope(self.retained)
        self.assertEqual(b, Q(1, 4))
        self.assertEqual(envelope([]), 0)
        self.assertEqual(value_at_x_one([], Q(3)), G())
        for base in (Q(1), Q(2), Q(3)):  # X=base^4 >= 1.
            for delta, gamma in self.retained:
                self.assertLessEqual(base**int(4*delta), base**int(4*b))
                for eta, tau in self.retained:
                    self.assertLessEqual(base**int(4*(delta+eta)), base**int(8*b))
        eta_star = Q(1, 2)-b
        self.assertEqual(2*b, 1-2*eta_star)

    def test_rh_envelope_specialization(self):
        on_line = [(Q(0), gamma) for delta, gamma in self.full]
        self.assertEqual(envelope(on_line), 0)
        self.assertEqual(Q(1, 2)-envelope(on_line), Q(1, 2))

    def test_denominator_and_far_tail_majorants(self):
        for delta in (Q(-499, 1000), Q(-1, 4), Q(0), Q(1, 4), Q(499, 1000)):
            for v in (Q(-6), Q(-1), Q(0), Q(1, 7), Q(3)):
                denominator = 1+G(v, delta)*G(v, delta)
                self.assertGreaterEqual(denominator.real, Q(3, 4)*(1+v*v))
                self.assertGreater(norm_squared(denominator), 0)
        for t in (Q(0), Q(1), Q(3)):
            for gamma in (Q(-20), Q(-6), Q(6), Q(601, 100), Q(9)):
                self.assertGreaterEqual(abs(t-gamma), abs(gamma)/2)
                self.assertLessEqual(1/(1+(t-gamma)**2), 4/(gamma*gamma))

    def test_pair_weight_bound_for_small_heights(self):
        for delta, gamma in self.full:
            for eta, tau in self.full:
                b, d = delta-eta, gamma-tau
                denominator = 4-G(b, d)*G(b, d)
                self.assertGreaterEqual(denominator.real, 3+d*d)
                self.assertGreaterEqual(norm_squared(denominator), (3+d*d)**2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
