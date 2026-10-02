#!/usr/bin/env python3
"""Exact finite checks for the logarithmic-gap and additive triple claims.

Task: verification. Assumptions: UNCONDITIONAL for finite algebra.
Logarithms of primes are formal polynomial variables, never floating-point
approximations. Tests do not certify the analytic estimates or their limits.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import re
import unittest

from check_triple_master import factorization
from check_pair_rh_audit import field, id_list, indexed_blocks

ROOT = Path(__file__).resolve().parents[1]


def weight(x, n):
    return min(Q(n)/x, x/Q(n))


def polynomial_product(left, right):
    out = defaultdict(Q)
    for a, x in left.items():
        for b, y in right.items():
            out[tuple(sorted(a+b))] += x*y
    return dict(out)


def lambda_polynomial(n):
    factors = factorization(n)
    return {(next(iter(factors)),): Q(1)} if len(factors) == 1 else {}


def log_polynomial(n):
    return {(p,): Q(e) for p, e in factorization(n).items()}


def comparable(m, n):
    return m != n and m <= 2*n and n <= 2*m


class TripleOffDiagonalChecks(unittest.TestCase):
    def test_comparable_far_partition_and_ratio_boundaries(self):
        for m, n in product(range(2, 65), repeat=2):
            near = comparable(m, n)
            far = n > 2*m or m > 2*n
            self.assertEqual(int(near)+int(far)+int(m == n), 1)
            if near:
                self.assertLessEqual(max(m, n)**2, 2*m*n)
                self.assertGreater(abs(m-n), 0)
        self.assertTrue(comparable(2, 4))
        self.assertTrue(comparable(4, 2))
        self.assertFalse(comparable(2, 5))
        self.assertFalse(comparable(4, 4))

    def test_harmonic_rows_columns_and_pair_cauchy_schwarz(self):
        for m in range(2, 50):
            row = sum((Q(1, abs(m-n)) for n in range(2, 2*m+1)
                       if comparable(m, n)), Q())
            harmonic = sum((Q(1, h) for h in range(1, 2*m+1)), Q())
            self.assertLessEqual(row, 2*harmonic)
            column = sum((Q(1, abs(m-n)) for n in range(2, 2*m+1)
                          if comparable(n, m)), Q())
            self.assertEqual(row, column)
        # u_m and v_n are arbitrary rational weighted coefficients here.
        u = {n: Q(n+1, 7) for n in range(2, 13)}
        v = {n: Q(2*n-1, 11) for n in range(2, 13)}
        pairs = [(m, n) for m, n in product(u, v) if comparable(m, n)]
        total = sum((u[m]*v[n]/abs(m-n) for m, n in pairs), Q())
        left = sum((u[m]**2/abs(m-n) for m, n in pairs), Q())
        right = sum((v[n]**2/abs(m-n) for m, n in pairs), Q())
        self.assertLessEqual(total**2, left*right)

    def test_multiplicative_weight_inequality_and_endpoints(self):
        for X, Y in product((Q(1), Q(3, 2), Q(4), Q(9)), repeat=2):
            for m, n in product(range(1, 16), repeat=2):
                self.assertLessEqual(weight(X, m)*weight(Y, n), weight(X*Y, m*n))
        self.assertEqual(weight(Q(4), 4), 1)
        self.assertEqual(weight(Q(1), 2), Q(1, 2))

    def test_formal_divisor_identity_and_convolution_envelope(self):
        for r in range(2, 97):
            divisor_sum = defaultdict(Q)
            conv = defaultdict(Q)
            weighted = defaultdict(Q)
            X, Y = Q(3, 2), Q(5)
            for d in range(1, r+1):
                if r % d:
                    continue
                for key, value in lambda_polynomial(d).items():
                    divisor_sum[key] += value
                term = polynomial_product(lambda_polynomial(d), lambda_polynomial(r//d))
                for key, value in term.items():
                    conv[key] += value
                    weighted[key] += value*weight(X, d)*weight(Y, r//d)
            self.assertEqual(dict(divisor_sum), log_polynomial(r))
            square = polynomial_product(log_polynomial(r), log_polynomial(r))
            for key in set(square) | set(conv) | set(weighted):
                self.assertLessEqual(conv[key], square.get(key, 0))
                # Common factor r^(-1/2) cancels in this coefficient comparison.
                self.assertLessEqual(weighted[key], weight(X*Y, r)*square.get(key, 0))

    def test_product_frequencies_group_without_losing_factorizations(self):
        powers = [n for n in range(2, 65) if len(factorization(n)) == 1]
        a = {n: Q(n+1, n*n) for n in powers[:8]}
        b = {n: Q(2*n+1, n*n) for n in powers[:10]}
        z = {n: Q(3*n+1, n*n) for n in powers}
        c = defaultdict(Q)
        for m, n in product(a, b):
            c[m*n] += a[m]*b[n]
        self.assertEqual(sum(c.values()), sum(a.values())*sum(b.values()))
        self.assertEqual(c[6], a[2]*b[3]+a[3]*b[2])
        direct, grouped = defaultdict(Q), defaultdict(Q)
        for m, n, k in product(a, b, z):
            direct[Q(m*n, k)] += a[m]*b[n]*z[k]
        for r, k in product(c, z):
            grouped[Q(r, k)] += c[r]*z[k]
        self.assertEqual(dict(direct), dict(grouped))
        diagonal = sum((c[r]*z[r] for r in c.keys() & z.keys()), Q())
        self.assertEqual(diagonal, grouped[Q(1)])
        classified = Q()
        for m, n in product(a, b):
            if m*n in z:
                self.assertEqual(set(factorization(m)), set(factorization(n)))
                classified += a[m]*b[n]*z[m*n]
        self.assertEqual(diagonal, classified)
        signed_off = {freq: -value for freq, value in grouped.items() if freq != 1}
        self.assertNotIn(Q(1), signed_off)
        self.assertEqual(-sum(grouped.values())+diagonal, sum(signed_off.values()))

    def test_dyadic_partition_count_weight_and_log_argument_bounds(self):
        for x in (Q(1), Q(3, 2), Q(2), Q(7, 2), Q(5)):
            for n in range(2, 129):
                memberships = int(n <= x)
                memberships += sum(2**j*x < n <= 2**(j+1)*x for j in range(8))
                self.assertEqual(memberships, 1)
            for j in range(6):
                numbers = [n for n in range(2, int(2**(j+1)*x)+1)
                           if 2**j*x < n <= 2**(j+1)*x]
                self.assertLessEqual(len(numbers), 2**(j+1)*x)
                for n in numbers:
                    self.assertLessEqual(weight(x, n)**2, Q(1, 2**(2*j)))
                    # Taking logs gives log(2n) <= (j+2)log(2x).
                    self.assertLessEqual(2*n, (2*x)**(j+2))
                self.assertLessEqual(sum((weight(x, n)**2 for n in numbers), Q()),
                                     2*x*Q(1, 2**j))

    def test_mixed_prefactors_and_fourier_conjugation(self):
        # Perfect-square bases make sqrt(XZ)/Y exact without numerical radicals.
        for xroot, yroot in product((Q(1), Q(2), Q(3)), repeat=2):
            X, Y = xroot**2, yroot**2
            self.assertEqual((xroot*xroot*yroot)/Y, X/yroot)
            self.assertEqual((yroot*yroot*xroot)/X, Y/xroot)
        for T, p, lam in product((Q(3), Q(7)), (Q(5), Q(9)), (Q(-2), Q(3))):
            xi = T*lam/p  # p denotes the formal constant 2*pi.
            self.assertEqual(-p*xi, -T*lam)
            self.assertEqual(1/(p*abs(xi)), 1/(T*abs(lam)))

    def test_growing_range_exponents_at_all_vertices(self):
        for eps in (Q(1, 1000), Q(1, 10), Q(1, 4), Q(333, 1000)):
            self.assertTrue(0 < eps < Q(1, 3))
            vertices = ((eps, eps), (eps, 1-2*eps), (1-2*eps, eps))
            for a, b in vertices:
                self.assertGreaterEqual(a, eps)
                self.assertGreaterEqual(b, eps)
                self.assertLessEqual(a+b, 1-eps)
                exponents = {
                    'archcube': (-2*(a+b), -4*eps),
                    'PPA': (-1-(a+b)/2, -1-eps),
                    'PAA': (-1-a/2-2*b, -1-Q(5, 2)*eps),
                    'APA': (-1-b/2-2*a, -1-Q(5, 2)*eps),
                    'AAP': (-1-(a+b)/2, -1-eps),
                    'PAP_off': (-1+a-b/2, -eps),
                    'APP_off': (-1+b-a/2, -eps),
                    'PPP_off': (-1+a+b, -eps)}
                for actual, upper in exponents.values():
                    self.assertLessEqual(actual, upper)
                    self.assertLessEqual(upper, -eps)
                for base in (a, b, a+b):
                    self.assertLessEqual(base/2-2, -(3+eps)/2)
                    self.assertLessEqual(-1-Q(5, 2)*base, -1-Q(5, 2)*eps)
                    self.assertLessEqual(-base, -eps)

    def test_remainder_word_counts_and_global_log_losses(self):
        words = [w for w in product('PAH', repeat=3) if 'H' in w]
        self.assertEqual(Counter(w.count('P') for w in words), {2: 3, 1: 9, 0: 7})
        for word in words:
            # H<=T^-eps, A<=T^-eps L, P<=sqrt(W_inf L).
            t_power = -sum(c != 'P' for c in word)
            log_power = Q(word.count('P'), 2)+word.count('A')
            self.assertLessEqual(t_power, -1)
            self.assertLessEqual(log_power, 2)
        for W in (Q(0), Q(1, 4), Q(1), Q(9)):
            self.assertLessEqual(W, (1+W)**2)  # sqrt(W)<=1+W.
        T = Q(3)
        self.assertEqual(2+2/T, Q(8, 3))
        for T in (Q(3), Q(7), Q(100)):
            self.assertLessEqual(2+2/T, Q(8, 3))
        for q, L in ((Q(1), Q(2)), (Q(2), Q(5)), (Q(3), Q(3))):
            self.assertLessEqual(L**3-q**3, 3*(L-q)*L**2)

    def test_ledger_sources_and_preserved_claim_scope(self):
        blocks = indexed_blocks((ROOT / 'research/theorem-ledger.yaml').read_text())
        expected = {
            'TRIPLE-LOG-GAP-001': ('lem:triple-log-gap', set()),
            'TRIPLE-OFFDIAG-001': ('lem:triple-offdiag',
                                 {'TRIPLE-LOG-GAP-001', 'TRIPLE-UNIFORM-001', 'TRIPLE-MASTER-001'}),
            'TRIPLE-SMOOTHED-ADDITIVE-001': ('cor:triple-smoothed-additive',
                                          {'TRIPLE-UNIFORM-001', 'TRIPLE-OFFDIAG-001'})}
        tex = (ROOT / 'proofs/triple_explicit_formula.tex').read_text()
        for claim, (label, dependencies) in expected.items():
            block = blocks[claim]
            self.assertEqual(field(block, 'status'), 'proved-draft')
            self.assertEqual(id_list(field(block, 'assumptions')), ['UNCONDITIONAL'])
            self.assertEqual(field(block, 'computation_used_in_proof'), 'false')
            self.assertEqual(field(block, 'all_limit_interchanges_justified'), 'true')
            self.assertEqual(set(id_list(field(block, 'dependencies'))), dependencies)
            self.assertIn('label: '+label, block)
            self.assertIn(r'\label{'+label+'}', tex)
        md = (ROOT / 'research/triple-error-budget.md').read_text()
        for label, _ in expected.values():
            self.assertIn(label, md)
        self.assertIn('not relative error', md)
        self.assertIn('is not a proved Fourier-support region', md)
        self.assertIn('No asymptotic main term', blocks['TRIPLE-UNIFORM-001'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
