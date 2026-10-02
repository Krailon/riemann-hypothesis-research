#!/usr/bin/env python3
"""Exact finite regression checks for TRIPLE-MASTER-001.

Task: verification. Algebra assumptions: UNCONDITIONAL. Zero fixtures:
SYNTHETIC_MODEL, with functional-equation/conjugation symmetry and multiplicity.
Standard-library rational arithmetic and formal phases only; no numerical
proof certificate, analytic limit verification, or empirical assertion on RH.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G, occurrences
from check_pair_rh_audit import field, id_list, indexed_blocks

ROOT = Path(__file__).resolve().parents[1]


def multiply(left, right):
    """Convolve coefficients of the two formal log-base phases."""
    result = defaultdict(G)
    for (a, b), v in left.items():
        for (c, d), w in right.items():
            result[a+c, b+d] += v*w
    return dict(result)


def zero_factor(zeros, base, t, slot, conjugated=False):
    result = defaultdict(G)
    for delta, gamma in zeros:
        z = G(t-gamma, delta)
        value = 2*base**int(4*delta)/(1+z*z)
        phase = gamma-t
        if conjugated:
            phase, value = -phase, value.conjugate()
        key = (phase, 0) if slot == 0 else (0, phase) if slot == 1 else (phase, phase)
        result[key] += value
    return dict(result)


def triple_coefficients(zeros, xbase, ybase, t):
    result = defaultdict(G)
    for (d, g), (e, h), (f, k) in product(zeros, repeat=3):
        u, v, w = G(t-g, d), G(t-h, e), G(t-k, -f)
        amplitude = 8*xbase**int(4*(d+f))*ybase**int(4*(e+f))
        result[g-k, h-k] += amplitude/((1+u*u)*(1+v*v)*(1+w*w))
    return dict(result)


def pattern(j, k, ell):
    if j == k == ell:
        return '123'
    if j == k:
        return '12|3'
    if j == ell:
        return '13|2'
    if k == ell:
        return '23|1'
    return '1|2|3'


def factorization(n):
    factors = Counter()
    p = 2
    while p*p <= n:
        while n % p == 0:
            factors[p] += 1
            n //= p
        p += 1
    if n > 1:
        factors[n] += 1
    return factors


class TripleMasterChecks(unittest.TestCase):
    def test_documented_words_signs_and_third_conjugation(self):
        md = (ROOT / 'research/triple-master-bookkeeping.md').read_text()
        tex = (ROOT / 'proofs/triple_explicit_formula.tex').read_text()
        md_rows = re.findall(
            r'^\| ([PAH]{3}) \| ([+-]) \| \\\((.*?)\\\) \| (yes|no) \|$', md, re.M)
        tex_rows = re.findall(
            r'^([PAH]{3}) & \$([+-])\$ & \$(.*?)\$ & (yes|no)\\\\$', tex, re.M)
        words = {''.join(w) for w in product('PAH', repeat=3)}
        for rows in (md_rows, tex_rows):
            self.assertEqual(len(rows), 27)
            self.assertEqual({r[0] for r in rows}, words)
            self.assertEqual(Counter(r[3] for r in rows), {'yes': 19, 'no': 8})
            for word, sign, integrand, has_h in rows:
                self.assertEqual(sign, '-' if word.count('P') % 2 else '+')
                self.assertEqual(integrand,
                                 word[0]+'_X'+word[1]+'_Y'+r'\overline{'+word[2]+'_Z}')
                self.assertEqual(has_h, 'yes' if 'H' in word else 'no')

    def test_27_term_product_and_four_remainder_refinements(self):
        # Non-real third-slot values detect a missing conjugation.
        slots = [dict(P=G(2, 3), A=G(5), H=G(-1, 2)),
                 dict(P=G(3, -2), A=G(7), H=G(4, 1)),
                 dict(P=G(-2, 5), A=G(11), H=G(3, -7))]
        values = [-s['P']+s['A']+s['H'] for s in slots]
        expected = values[0]*values[1]*values[2].conjugate()
        expanded = sum(((-1)**w.count('P') * slots[0][w[0]] * slots[1][w[1]]
                        * slots[2][w[2]].conjugate()
                        for w in product('PAH', repeat=3)), G())
        self.assertEqual(expanded, expected)
        refined = []
        for s in slots:
            a, b, c = G(1, 2), G(-3, 4), G(5, -6)
            refined.append([-s['P'], s['A'], a, b, c, s['H']-a-b-c])
        terms = [a*b*c.conjugate() for a, b, c in product(*refined)]
        self.assertEqual(len(terms), 216)
        self.assertEqual(sum(terms, G()), expected)

    def test_zero_product_phase_cancellation_and_factor_eight(self):
        zeros = occurrences()
        for x, y, t in ((Q(1), Q(1), Q(3)), (Q(2), Q(3), Q(7, 2))):
            direct = multiply(multiply(zero_factor(zeros, x, t, 0),
                                       zero_factor(zeros, y, t, 1)),
                              zero_factor(zeros, x*y, t, 2, conjugated=True))
            self.assertEqual(direct, triple_coefficients(zeros, x, y, t))

    def test_five_index_patterns_weighted_partition(self):
        for q in range(7):
            triples = list(product(range(q), repeat=3))
            counts = Counter(pattern(*row) for row in triples)
            expected = {'123': q, '12|3': q*(q-1), '13|2': q*(q-1),
                        '23|1': q*(q-1), '1|2|3': q*(q-1)*(q-2)}
            for name, count in expected.items():
                self.assertEqual(counts[name], count)
            # Independently sum five parametrizations with arbitrary complex weights.
            a = [G(j+1, j-2) for j in range(q)]
            b = [G(2*j-1, j+3) for j in range(q)]
            c = [G(j+4, 1-j) for j in range(q)]
            term = lambda j, k, ell: a[j]*b[k]*c[ell].conjugate()
            separate = sum((term(j, j, j) for j in range(q)), G())
            separate += sum((term(j, j, k)+term(j, k, j)+term(j, k, k)
                             for j in range(q) for k in range(q) if j != k), G())
            separate += sum((term(*row) for row in triples if len(set(row)) == 3), G())
            self.assertEqual(separate, sum(a, G())*sum(b, G())*sum(c, G()).conjugate())

    def test_occurrences_are_not_complex_zeros_or_ordinates(self):
        zeros = occurrences()
        self.assertEqual(Counter(zeros), Counter((-d, g) for d, g in zeros))
        self.assertEqual(Counter(zeros), Counter((d, -g) for d, g in zeros))
        triples = list(product(range(len(zeros)), repeat=3))
        index_diag = sum(j == k == ell for j, k, ell in triples)
        complex_diag = sum(zeros[j] == zeros[k] == zeros[ell] for j, k, ell in triples)
        ordinate_diag = sum(zeros[j][1] == zeros[k][1] == zeros[ell][1]
                            for j, k, ell in triples)
        self.assertLess(index_diag, complex_diag)
        self.assertLess(complex_diag, ordinate_diag)

    def test_swap_and_horizontal_reflection(self):
        zeros = occurrences()
        original = triple_coefficients(zeros, Q(2), Q(3), Q(4))
        swapped = triple_coefficients(zeros, Q(3), Q(2), Q(4))
        self.assertEqual(original, {(b, a): v for (a, b), v in swapped.items()})
        self.assertEqual(original, triple_coefficients([(-d, g) for d, g in zeros],
                                                       Q(2), Q(3), Q(4)))
        self.assertEqual(triple_coefficients([], Q(1), Q(2), Q(4)), {})

    def test_denominator_majorant_exact_squared_form(self):
        # The analytic proof uses Re D >= (3/4)(1+v^2).
        for delta, v in product((Q(-1, 2), Q(-1, 4), Q(0), Q(1, 2)),
                                (Q(-7), Q(0), Q(3, 2))):
            d = G(1+v*v-delta*delta, 2*v*delta)
            lower = Q(3, 4)*(1+v*v)
            self.assertGreaterEqual(d.real, lower)
            self.assertGreaterEqual(d.real*d.real+d.imag*d.imag, lower*lower)

    def test_fourier_frequency_sign_and_units(self):
        # Formal coefficients in independent log(m), log(n), log(k).
        # p stands for 2*pi; exact rational substitution checks its cancellation.
        prime_phase = (-1, -1, 1)
        log_ratio = (1, 1, -1)
        for T, p in ((Q(3), Q(7)), (Q(13, 2), Q(22, 3))):
            transformed_frequency = tuple(T*c/p for c in log_ratio)
            self.assertEqual(tuple(-p*c for c in transformed_frequency),
                             tuple(T*c for c in prime_phase))
            self.assertEqual(T*(1/T), 1)  # dt/T=du.
        # log(XY)=log X+log Y in the center phases.
        self.assertEqual(tuple(a+b+c for a, b, c in zip((-1, 0), (0, -1), (1, 1))),
                         (0, 0))

    def test_prime_power_resonance_classification(self):
        limit = 128
        powers = {n for n in range(2, limit+1) if len(factorization(n)) == 1}
        direct = {(m, n, m*n) for m, n in product(powers, repeat=2) if m*n in powers}
        generated = set()
        for p in range(2, limit+1):
            if factorization(p) != Counter({p: 1}):
                continue
            for a, b in product(range(1, 8), repeat=2):
                if p**(a+b) <= limit:
                    generated.add((p**a, p**b, p**(a+b)))
        self.assertEqual(direct, generated)
        self.assertIn((2, 4, 8), direct)
        self.assertIn((4, 2, 8), direct)  # Ordered; no factor 1/2.
        self.assertNotIn((2, 3, 6), direct)

    def test_pair_form_with_constant_second_input(self):
        f, h = G(2, 3), G(5, -7)
        self.assertEqual(f*G(1)*h.conjugate(), G(-11, 29))
        # Constant 1 removes a slot algebraically, unlike setting its base to 1.
        at_one = zero_factor(occurrences(), Q(1), Q(3), 1)
        self.assertNotEqual(at_one, {(0, 0): G(1)})

    def test_ledger_source_and_dependency_graph(self):
        blocks = indexed_blocks((ROOT / 'research/theorem-ledger.yaml').read_text())
        block = blocks['TRIPLE-MASTER-001']
        self.assertEqual(field(block, 'status'), 'proved-draft')
        self.assertEqual(id_list(field(block, 'assumptions')), ['UNCONDITIONAL'])
        self.assertEqual(field(block, 'computation_used_in_proof'), 'false')
        self.assertEqual(set(id_list(field(block, 'dependencies'))),
                         {'PAIR-EF-CONVERGENCE-001', 'PAIR-EF-001', 'PAIR-COUNT-KERNEL-001'})
        self.assertIn('file: proofs/triple_explicit_formula.tex', block)
        self.assertIn('label: lem:triple-master', block)
        tex = (ROOT / 'proofs/triple_explicit_formula.tex').read_text()
        self.assertIn(r'\label{lem:triple-master}', tex)
        labels = re.findall(r'\\label\{([^}]+)\}', tex)
        self.assertEqual(len(labels), len(set(labels)))
        self.assertTrue(set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)) <= set(labels))
        visited, active = set(), set()

        def visit(key):
            self.assertIn(key, blocks)
            self.assertNotIn(key, active)
            if key in visited:
                return
            active.add(key)
            if re.search(r'^    dependencies: ', blocks[key], re.M):
                dependencies = id_list(field(blocks[key], 'dependencies'))
            elif re.search(r'^    dependencies:$', blocks[key], re.M):
                match = re.search(r'^    dependencies:\n((?:      - [A-Z0-9-]+\n)+)',
                                  blocks[key], re.M)
                self.assertIsNotNone(match)
                dependencies = re.findall(r'      - ([A-Z0-9-]+)', match[1])
            else:
                dependencies = []
            for dependency in dependencies:
                visit(dependency)
            active.remove(key)
            visited.add(key)

        for key in blocks:
            visit(key)


if __name__ == '__main__':
    unittest.main(verbosity=2)
