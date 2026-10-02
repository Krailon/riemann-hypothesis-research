#!/usr/bin/env python3
"""Exact finite regression checks for TRIPLE-UNIFORM-001.

Task: verification. Assumptions: UNCONDITIONAL for algebra and inequalities.
Rational finite fixtures check accounting; they do not certify analytic
prime estimates, asymptotics, or numerical statements about zeta zeros.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G
from check_pair_rh_audit import field, id_list, indexed_blocks

ROOT = Path(__file__).resolve().parents[1]
ERRORS = ('arch', 'DS', 'pole', 'trivial')
WORDS = tuple(''.join(w) for w in product('PAH', repeat=3))
H_WORDS = tuple(w for w in WORDS if 'H' in w)


def norm_squared(z):
    return z.real*z.real + z.imag*z.imag


def integrate(a, b, c, weights):
    return sum((weight*x*y*z.conjugate()
                for weight, x, y, z in zip(weights, a, b, c)), G())


def refinements(word):
    """Ordered substitutions keep positions even when remainder names repeat."""
    for choices in product(ERRORS, repeat=word.count('H')):
        sequence = iter(choices)
        yield tuple(next(sequence) if letter == 'H' else letter for letter in word)


def norm_majorant_squared(x, T, b_squared, C_M_squared, W_inf, ell):
    """Exact arithmetic on supplied squared primitives, not approximate logs."""
    if x <= 2*T:
        return min(b_squared, C_M_squared*W_inf*ell)
    return b_squared


def fixture():
    weights = (Q(1, 6), Q(1, 3), Q(1, 2))
    slots = []
    for i in range(3):
        slot = {'P': [G(i+j+1, 2*i-j) for j in range(3)],
                'A': [G(Q(j+2, i+1)) for j in range(3)]}
        for k, name in enumerate(ERRORS):
            slot[name] = [G(Q(i+k+1, j+2), Q(j-k, i+2)) for j in range(3)]
        slot['H'] = [sum((slot[name][j] for name in ERRORS), G()) for j in range(3)]
        slots.append(slot)
    return weights, slots


class TripleUniformChecks(unittest.TestCase):
    def test_complete_budget_table_and_ordered_bound_assignments(self):
        md = (ROOT / 'research/triple-error-budget.md').read_text()
        rows = re.findall(
            r'^\| ([PAH]{3}) \| ([+-]) \| \\\((.*?)\\\) \| (\d+) \|$', md, re.M)
        self.assertEqual(len(rows), 19)
        self.assertEqual({row[0] for row in rows}, set(H_WORDS))
        letters = {'P': 'm', 'A': r'\alpha', 'H': 'h'}
        for word, sign, bound, count in rows:
            self.assertEqual(sign, '-' if word.count('P') % 2 else '+')
            self.assertEqual(bound, ''.join(letters[w]+'_'+x for w, x in zip(word, 'XYZ')))
            self.assertEqual(int(count), 4**word.count('H'))
        self.assertEqual(sum(int(row[3]) for row in rows), 208)
        all_rows = re.findall(r'^\| ([PAH]{3}) \|', md, re.M)
        self.assertEqual(Counter(all_rows), Counter(WORDS))

    def test_208_components_are_a_disjoint_partition(self):
        expanded = [row for w in H_WORDS for row in refinements(w)]
        direct = [row for row in product(('P', 'A')+ERRORS, repeat=3)
                  if any(letter in ERRORS for letter in row)]
        self.assertEqual(len(expanded), 208)
        self.assertEqual(Counter(expanded), Counter(direct))
        self.assertEqual(Counter(w.count('H') for w in H_WORDS), {1: 12, 2: 6, 3: 1})

    def test_refined_errors_equal_signed_aggregates(self):
        weights, slots = fixture()
        for word in H_WORDS:
            sign = (-1)**word.count('P')
            direct = sign*integrate(*(slots[i][word[i]] for i in range(3)), weights)
            expanded = sum((sign*integrate(*(slots[i][row[i]] for i in range(3)), weights)
                            for row in refinements(word)), G())
            self.assertEqual(direct, expanded)

    def test_component_bounds_use_correct_norms(self):
        weights, slots = fixture()
        self.assertEqual(sum(weights), 1)
        for word in H_WORDS:
            for row in refinements(word):
                factors = [slots[i][row[i]] for i in range(3)]
                upper_squared = Q(1)
                for letter, values in zip(row, factors):
                    if letter == 'P':
                        upper_squared *= sum(weight*norm_squared(value)
                                             for weight, value in zip(weights, values))
                    else:
                        upper_squared *= max(map(norm_squared, values))
                actual = integrate(*factors, weights)
                self.assertLessEqual(norm_squared(actual), upper_squared)

    def test_cubic_three_sup_norm_choices(self):
        weights, slots = fixture()
        factors = [slot['P'] for slot in slots]
        bounds = []
        for chosen in range(3):
            upper_squared = Q(1)
            for i, values in enumerate(factors):
                upper_squared *= (max(map(norm_squared, values)) if i == chosen else
                                  sum(w*norm_squared(v) for w, v in zip(weights, values)))
            bounds.append(upper_squared)
        self.assertLessEqual(norm_squared(integrate(*factors, weights)), min(bounds))

    def test_signed_retained_expression_reconstructs_direct_product(self):
        weights, slots = fixture()
        # Logs are formal rational samples, with a common log(t+2) at each node.
        X, Y, Z, q = Q(2), Q(3), Q(6), Q(1)
        logs = (Q(2), Q(3), Q(4))
        for slot, x in zip(slots, (X, Y, Z)):
            slot['A'] = [G(value/x) for value in logs]
        J1 = sum(w*v for w, v in zip(weights, logs))
        J3 = sum(w*v**3 for w, v in zip(weights, logs))
        dXZ, dYZ, resonance = Q(7, 3), Q(5, 4), Q(11, 7)
        row = lambda word: integrate(*(slots[i][word[i]] for i in range(3)), weights)
        retained = q**3/Z**2 + J1*dXZ/Y + J1*dYZ/X - resonance
        errors = G((J3-q**3)/Z**2)
        errors += row('PPA')-row('PAA')-row('APA')-row('AAP')
        errors += row('PAP')-J1*dXZ/Y
        errors += row('APP')-J1*dYZ/X
        errors += -row('PPP')+resonance
        errors += sum(((-1)**w.count('P')*row(w) for w in H_WORDS), G())
        full = [[-slot['P'][j]+slot['A'][j]+slot['H'][j] for j in range(3)]
                for slot in slots]
        self.assertEqual(G(retained)+errors, integrate(*full, weights))

    def test_mixed_prime_diagonals_and_frequency_orientation(self):
        # Formal log frequencies for n=2^a*3^b, all nonzero.
        indices = ((1, 0), (2, 0), (0, 1), (1, 1))
        left = dict(zip(indices, (Q(1), Q(2), Q(3), Q(5))))
        right = dict(zip(indices, (Q(7), Q(11), Q(13), Q(17))))
        mixed, same_sign = defaultdict(Q), defaultdict(Q)
        for (a, b), (c, d) in product(left, right):
            mixed[a-c, b-d] += left[a, b]*right[c, d]
            same_sign[a+c, b+d] += left[a, b]*right[c, d]
        self.assertEqual(mixed[0, 0], sum(left[n]*right[n] for n in indices))
        self.assertNotIn((0, 0), same_sign)
        for key, value in mixed.items():
            reflected = sum((right[n]*left[m] for n, m in product(indices, repeat=2)
                             if (n[0]-m[0], n[1]-m[1]) == (-key[0], -key[1])), Q())
            self.assertEqual(value, reflected)

    def test_norm_branch_endpoints_and_probability_normalization(self):
        for T in (Q(3), Q(11, 2)):
            for x in (Q(1), 2*T-Q(1, 10), 2*T):
                self.assertEqual(norm_majorant_squared(x, T, 100, 4, 2, 3), 24)
                self.assertEqual(norm_majorant_squared(x, T, 5, 4, 2, 3), 5)
            self.assertEqual(norm_majorant_squared(2*T+Q(1, 10), T, 100, 4, 2, 3), 100)
            C_pair, W_inf, ell = Q(7), Q(3), Q(5)
            self.assertEqual(W_inf/T*(C_pair*2*T*ell), (2*C_pair)*W_inf*ell)
        self.assertTrue(all(x <= 2*Q(3) for x in (Q(1), Q(6), Q(6))))
        self.assertEqual(Q(1)*Q(6), 2*Q(3))  # X=1, Y=6, XY=2T.

    def test_remainder_endpoint_and_oscillatory_scales(self):
        T = Q(3)
        for root_x in (Q(1), Q(2), Q(3)):
            x = root_x**2
            for t in (T, Q(7, 2), 2*T):
                self.assertLessEqual(4*root_x/(1+t*t), 4*root_x/(1+T*T))
                self.assertLessEqual(12/(root_x**5*(t+2)),
                                     12/(root_x**5*(T+2)))
        for r in (1, 2):
            L, W0, W1 = Q(5), Q(1), Q(7)
            for u in (Q(1), Q(3, 2), Q(2)):
                derivative_ratio = T/(T*u+2)
                self.assertLessEqual(derivative_ratio, 1)
                self.assertLessEqual(W1*L**r+r*W0*L**(r-1)*derivative_ratio,
                                     W1*L**r+r*W0*L**(r-1))
        # p denotes 2*pi. Its Fourier derivative factor cancels exactly.
        for lam in (Q(-3), Q(2)):
            p, omega_norm = Q(7), Q(11)
            xi = T*lam/p
            self.assertEqual(omega_norm/(p*abs(xi)), omega_norm/(T*abs(lam)))
        X, Y = Q(2), Q(5)
        Z = X*Y
        self.assertEqual(X*Y*Z, Z**2)
        self.assertEqual(T/T, 1)

    def test_archcube_and_geometric_constants_algebra(self):
        q, L = Q(2), Q(5)
        for value in (q, Q(3), L):
            self.assertLessEqual(value**3-q**3, L**3-q**3)
            self.assertGreaterEqual(value**3-q**3, 0)
        for ratio in (Q(1, 2), Q(7, 10)):
            for N in (1, 2, 7):
                self.assertEqual(sum((j+1)*ratio**j for j in range(N)),
                                 (1-(N+1)*ratio**N+N*ratio**(N+1))/(1-ratio)**2)
                self.assertEqual(sum(ratio**j for j in range(N)),
                                 (1-ratio**N)/(1-ratio))

    def test_ledger_source_and_budget_links(self):
        blocks = indexed_blocks((ROOT / 'research/theorem-ledger.yaml').read_text())
        block = blocks['TRIPLE-UNIFORM-001']
        self.assertEqual(field(block, 'status'), 'proved-draft')
        self.assertEqual(id_list(field(block, 'assumptions')), ['UNCONDITIONAL'])
        self.assertEqual(field(block, 'all_limit_interchanges_justified'), 'true')
        self.assertEqual(field(block, 'computation_used_in_proof'), 'false')
        self.assertEqual(set(id_list(field(block, 'dependencies'))),
                         {'TRIPLE-MASTER-001', 'PAIR-EF-001',
                          'PAIR-PRIME-MEAN-001', 'PAIR-PRIME-DIAGONAL-001'})
        self.assertIn('label: lem:triple-uniform', block)
        tex = (ROOT / 'proofs/triple_explicit_formula.tex').read_text()
        self.assertIn(r'\label{lem:triple-uniform}', tex)
        md_path = ROOT / 'research/triple-error-budget.md'
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', md_path.read_text()):
            self.assertTrue((md_path.parent / target).is_file(), target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
