#!/usr/bin/env python3
"""Exact finite checks for retained terms and the interior test-function theorem.

Task: verification. Assumptions: UNCONDITIONAL for algebra; finite zero
fixtures: SYNTHETIC_MODEL with the full quartet symmetries and multiplicity.
Logarithms and 2*pi are formal symbols evaluated at rational fixtures, not
floating-point approximations. The analytic arguments are in the proof.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G, I, occurrences
from check_pair_rh_audit import field, id_list, indexed_blocks
from check_triple_master import factorization
from check_triple_offdiag import weight

ROOT = Path(__file__).resolve().parents[1]


def derivative(poly):
    """Differentiate u^p log(u)^k exactly."""
    out = defaultdict(Q)
    for (p, k), coefficient in poly.items():
        if p:
            out[p-1, k] += p*coefficient
        if k:
            out[p-1, k-1] += k*coefficient
    return {key: value for key, value in out.items() if value}


def evaluate(poly, u, log_u):
    return sum((c*u**p*log_u**k for (p, k), c in poly.items()), Q())


def kernel_weight(a, b, u):
    return weight(a, u)*weight(b, u)/u


class TripleTestFunctionChecks(unittest.TestCase):
    def test_mixed_weight_joins_and_symmetry(self):
        for a, b in ((Q(1), Q(1)), (Q(1), Q(3)), (Q(3, 2), Q(5)), (Q(4), Q(4))):
            for u in (Q(1), a, (a+b)/2, b, 2*b):
                expected = u/(a*b) if u <= a else a/(b*u) if u <= b else a*b/u**3
                self.assertEqual(kernel_weight(a, b, u), expected)
                self.assertEqual(kernel_weight(a, b, u), kernel_weight(b, a, u))
            self.assertEqual(a/(a*b), a/(b*a))
            self.assertEqual(a/(b*b), a*b/b**3)

    def test_three_antiderivatives_and_mixed_integral(self):
        low = {(2, 1): Q(1, 2), (2, 0): Q(1, 4)}
        middle = {(0, 2): Q(1, 2), (0, 1): Q(1)}
        high = {(-2, 1): Q(-1, 2), (-2, 0): Q(-3, 4)}
        self.assertEqual(derivative(low), {(1, 1): Q(1), (1, 0): Q(1)})
        self.assertEqual(derivative(middle), {(-1, 1): Q(1), (-1, 0): Q(1)})
        self.assertEqual(derivative(high), {(-3, 1): Q(1), (-3, 0): Q(1)})
        fixtures = ((Q(1), Q(1), Q(0), Q(0)),
                    (Q(1), Q(3), Q(0), Q(2)),
                    (Q(2), Q(5), Q(1), Q(3)),
                    (Q(4), Q(4), Q(2), Q(2)))
        for a, b, la, lb in fixtures:
            integral = (evaluate(low, a, la)-evaluate(low, Q(1), Q(0)))/(a*b)
            integral += a/b*(evaluate(middle, b, lb)-evaluate(middle, a, la))
            integral -= a*b*evaluate(high, b, lb)
            r, h = a/b, lb-la
            closed = r/2*(1+h)*(la+lb)+r*(1+h)-1/(4*a*b)
            self.assertEqual(integral, closed)
            variation = (a*a-1)/(2*a*b) + r*h + 3*r/2
            self.assertEqual(variation, r*(2+h)-1/(2*a*b))
            if a == b:
                self.assertEqual(closed, la+1-1/(4*a*a))
                self.assertEqual(r/2*(1+h)*(la+lb), la)

    def test_signed_retained_evaluation_and_J_error(self):
        for X, Y, lx, ly in ((Q(1), Q(1), Q(0), Q(0)),
                             (Q(2), Q(3), Q(1), Q(2))):
            Z, q, mu, remainder = X*Y, Q(5), Q(1, 3), Q(1, 11)
            J1 = q+mu+remainder
            dx, dy, resonance = Q(-2, 7), Q(3, 8), Q(4, 9)
            leading_xz = (1+ly)*(2*lx+ly)/(2*Y)
            leading_yz = (1+lx)*(2*ly+lx)/(2*X)
            original = q**3/Z**2+J1*(leading_xz+dx)/Y+J1*(leading_yz+dy)/X-resonance
            Gxy = (1+ly)*(2*lx+ly)/(2*Y**2)+(1+lx)*(2*ly+lx)/(2*X**2)
            evaluated = q**3/Z**2+(q+mu)*Gxy+J1*(dx/Y+dy/X)+remainder*Gxy-resonance
            self.assertEqual(original, evaluated)
        for T, u in product((Q(3), Q(10)), (Q(1), Q(3, 2), Q(2))):
            self.assertLessEqual(2/(T*u), 2/T)

    def test_prime_power_resonance_envelope_with_ordered_factors(self):
        for p, k in product((2, 3, 5), range(2, 8)):
            r = p**k
            self.assertLessEqual(k-1, k**3)
            for X, Y in ((Q(1), Q(1)), (Q(3, 2), Q(5)), (Q(8), Q(8))):
                Z = X*Y
                # Coefficient of (log p)^3; common product sqrt(r)^2=r.
                actual = sum((weight(X, p**a)*weight(Y, p**(k-a))*weight(Z, r)/r
                              for a in range(1, k)), Q())
                self.assertLessEqual(actual, (k-1)*weight(Z, r)**2/r)
                self.assertLessEqual(actual, k**3*weight(Z, r)**2/r)
        bound = 400
        pp = {n for n in range(2, bound+1)
              if len(factorization(n)) == 1 and sum(factorization(n).values()) >= 2}
        all_powers = {a**k for a in range(2, 21) for k in range(2, 10) if a**k <= bound}
        self.assertTrue(pp <= all_powers)
        self.assertIn(16, pp)  # One integer, despite 2^4=4^2.
        self.assertNotIn(6, pp)

    def test_resonance_dyadic_split_and_weights(self):
        for Z in (Q(1), Q(3, 2), Q(4), Q(16)):
            for r in range(2, 129):
                low = [j for j in range(10) if Z/Q(2**(j+1)) < r <= Z/Q(2**j)]
                high = [j for j in range(10) if 2**j*Z < r <= 2**(j+1)*Z]
                self.assertEqual(len(low)+len(high), 1)
                value = weight(Z, r)**2/r
                for j in low:
                    self.assertLessEqual(value, Q(1, 2**j)/Z)
                for j in high:
                    self.assertLessEqual(value, Q(1, 2**(3*j))/Z)

    def test_retained_vanishing_exponents(self):
        for eps in (Q(1, 100), Q(1, 8), Q(3, 10)):
            for a, b in ((eps, eps), (eps, 1-2*eps), (1-2*eps, eps)):
                exponents = (-2*(a+b), -2*a, -2*b, -(a+b)/2)
                self.assertLessEqual(exponents[0], -4*eps)
                self.assertLessEqual(exponents[1], -2*eps)
                self.assertLessEqual(exponents[2], -2*eps)
                self.assertLessEqual(exponents[3], -eps)
                self.assertTrue(all(exponent <= -eps for exponent in exponents))

    def test_complex_arguments_anchor_and_factor_eight(self):
        zeros = occurrences()
        self.assertEqual(Counter(zeros), Counter((-d, g) for d, g in zeros))
        p, logT, log2pi = Q(7), Q(9), Q(2)  # Formal constants and logarithms.
        logB, xi, eta = logT-log2pi, Q(1, 5), Q(1, 4)
        L = logB/p
        for anchor, second, third in zip(zeros, zeros[2:]+zeros[:2], zeros[5:]+zeros[:5]):
            d1, g1 = anchor
            d2, g2 = second
            d3, g3 = third
            z21, z31 = G(L*(g2-g1), -L*(d2+d1)), G(L*(g3-g1), -L*(d3+d1))
            fourier_exponent = p*I*(xi*z21+eta*z31)
            power_exponent = logB*(xi*G(d2+d1, g2-g1)+eta*G(d3+d1, g3-g1))
            self.assertEqual(fourier_exponent, power_exponent)
            self.assertEqual(z21.imag, -L/logT*(d2*logT+d1*logT))
            t = Q(8)
            u1, u2, u3 = G(t-g1, d1), G(t-g2, d2), G(t-g3, d3)
            D1, D2, D3 = 1+u1*u1, 1+u2*u2, 1+u3*u3
            self.assertEqual((2/D2)*(2/D3)*(2/D1).conjugate(),
                             8/(D2*D3*D1.conjugate()))
            self.assertEqual(D2*D3, D3*D2)

    def test_exact_spacing_margin_transfer_and_support_example(self):
        eps = Q(1, 8)
        for q, c in ((Q(9), Q(2)), (Q(3), Q(299, 100)), (Q(100), Q(2))):
            theta = (q-c)/q
            self.assertTrue(0 < theta < 1)
            epsT = eps*theta
            for xi, eta in ((eps, eps), (eps, 1-2*eps), (1-2*eps, eps)):
                self.assertGreaterEqual(theta*xi, epsT)
                self.assertGreaterEqual(theta*eta, epsT)
                self.assertLessEqual(theta*(xi+eta), 1-epsT)
            self.assertEqual(-epsT*q, -eps*(q-c))
        for xi, eta in product((Q(3, 16), Q(5, 16)), repeat=2):
            self.assertGreaterEqual(xi, eps)
            self.assertGreaterEqual(eta, eps)
            self.assertLessEqual(xi+eta, 1-eps)
        self.assertGreater(eps, 0)  # Axes are not included.
        self.assertLess(1-eps, 1)

    def test_new_claims_labels_links_and_support_declaration(self):
        blocks = indexed_blocks((ROOT / 'research/theorem-ledger.yaml').read_text())
        claims = {
            'TRIPLE-RETAINED-001': ('lem:triple-retained',
                                  {'TRIPLE-UNIFORM-001', 'TRIPLE-OFFDIAG-001', 'PRIME-PNT-001'}),
            'TRIPLE-INTERIOR-VANISHING-001': ('cor:triple-interior-vanishing',
                                            {'TRIPLE-RETAINED-001', 'TRIPLE-SMOOTHED-ADDITIVE-001'}),
            'TRIPLE-TEST-FUNCTION-001': ('thm:triple-test-function',
                                       {'TRIPLE-INTERIOR-VANISHING-001', 'TRIPLE-MASTER-001'})}
        tex = (ROOT / 'proofs/triple_explicit_formula.tex').read_text()
        md_path = ROOT / 'research/triple-test-functions.md'
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
        self.assertIn('SUPPORT(compact subset of xi>0, eta>0, xi+eta<1)',
                      field(blocks['TRIPLE-TEST-FUNCTION-001'], 'assumptions'))
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', md):
            self.assertTrue((md_path.parent / target).is_file(), target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
