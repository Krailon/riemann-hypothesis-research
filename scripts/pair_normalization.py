"""Regenerate PAIR-ASYMPTOTIC-001 normalization with exact monomial algebra.

Task: verification/exposition. Assumptions: UNCONDITIONAL.
Analytic estimates are imported from the local proved-draft manuscript.
This module neither proves those estimates nor creates a numerical certificate.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
import json
import re


@dataclass(frozen=True)
class Monomial:
    coefficient: Q
    powers: tuple

    @classmethod
    def make(cls, coefficient=1, **powers):
        return cls(Q(coefficient), tuple(sorted(
            (k, Q(v)) for k, v in powers.items() if v != 0)))

    def divide(self, other):
        powers = dict(self.powers)
        for name, exponent in other.powers:
            powers[name] = powers.get(name, Q(0)) - exponent
        return self.make(self.coefficient / other.coefficient, **powers)

    def substitute_base(self):
        # X=T^a and l=log X=a*q; a=|alpha| is used after evenness.
        powers = dict(self.powers)
        powers['v'] = powers.pop('X', Q(0))  # v denotes T^a
        log_power = powers.pop('l', Q(0))
        powers['q'] = powers.get('q', Q(0)) + log_power
        powers['a'] = powers.get('a', Q(0)) + log_power
        return self.make(self.coefficient, **powers)

    def endpoint(self, alpha):
        a = abs(Q(alpha))
        powers = dict(self.powers)
        powers['T'] = powers.get('T', Q(0)) + a*powers.pop('v', Q(0))
        a_power = powers.pop('a', Q(0))
        if a_power.denominator != 1:
            raise ValueError('endpoint requires an integer power of a')
        return self.make(self.coefficient * a**int(a_power), **powers)

    def expression(self):
        if not self.coefficient:
            return '0'
        factors = [] if self.coefficient == 1 else [str(self.coefficient)]
        for name, exponent in self.powers:
            if name == 'v':
                factors.append('T^a' if exponent == 1 else f'T^({exponent}*a)')
            else:
                factors.append(name if exponent == 1 else f'{name}^({exponent})')
        return ' * '.join(factors) or '1'

    def record(self):
        return {'coefficient': str(self.coefficient),
                'powers': {k: str(v) for k, v in self.powers},
                'expression': self.expression()}


def source(claim, label):
    return {'claim_id': claim, 'file': 'proofs/pair_baseline.tex', 'label': label}


def assembly_inputs():
    """Bounds and main terms from eq:pair-assembly, before normalization."""
    m = Monomial.make
    return [
        ('archimedean_main', 'main', m(T=1, X=-2, q=2),
         source('PAIR-RHS-MEAN-001', 'eq:rhs-mean')),
        ('prime_main', 'main', m(T=1, l=1),
         source('PAIR-RHS-MEAN-001', 'eq:rhs-mean')),
        ('E_peak', 'error', m(T=1, q=1, X=-2),
         source('PAIR-RHS-MEAN-001', 'eq:rhs-mean')),
        ('E_mean', 'error', m(T=1, q=Q(1, 2)),
         source('PAIR-RHS-MEAN-001', 'eq:rhs-mean')),
        ('E_compare_T', 'error', m(T=1),
         source('PAIR-COMPARE-001', 'eq:pair-compare')),
        ('E_compare_X', 'error', m(X=1),
         source('PAIR-COMPARE-001', 'eq:pair-compare')),
    ]


def generate():
    divisor = Monomial.make(T=1, q=1)
    rows, normalized = [], {}
    for name, kind, before, locator in assembly_inputs():
        after = before.divide(divisor)
        normalized[name] = after
        rows.append({'id': name, 'kind': kind, 'source': locator,
                     'before_normalization': before.record(),
                     'after_normalization': after.record(),
                     'after_substitution': after.substitute_base().record()})
    main = [normalized[k].substitute_base() for k in
            ('archimedean_main', 'prime_main')]
    errors = [normalized[k].substitute_base() for k in ('E_peak', 'E_mean')]
    return {
        'schema_version': 1, 'claim_id': 'PAIR-ASYMPTOTIC-001',
        'claim_status': 'proved-draft', 'task': 'verification_and_exposition',
        'assumptions': ['UNCONDITIONAL'], 'analytic_proof_certificate': False,
        'definitions': {'q': 'log T', 'l': 'log X', 'a': '|alpha|', 'v': 'T^a',
                        'C_T': 'T log T / (2 pi)'},
        'domains': ['T>=3', '1<=X<=T', 'q=log T>1', '|alpha|<=1'],
        'normalization': {'quantity': '2 pi Phi / (T q) = Phi / C_T',
                          'divisor': divisor.record(),
                          'source': source('PAIR-ASYMPTOTIC-001', 'eq:pair-normalization')},
        'rows': rows,
        'comparison_signs': {
            'L_minus_2piPhi': {'E_trunc': 1, 'E_height': 1, 'E_extension': 1},
            '2piPhi_minus_L': {'E_trunc': -1, 'E_height': -1, 'E_extension': -1},
            'domain': 'T>=5, Z=T log^2 T, 1<=X<=T',
            'small_height': 'For 3<=T<5 use E_compare_X=2 pi Phi-L and E_compare_T=0.',
            'source': source('PAIR-TRUNC-001', 'eq:trunc-decomposition')},
        'absorption': {
            'comparison_X_over_comparison_T': normalized['E_compare_X'].divide(
                normalized['E_compare_T']).record(),
            'comparison_T_over_mean': normalized['E_compare_T'].divide(
                normalized['E_mean']).record(),
            'justification': 'X/T<=1 and q^(-1/2)<=1. Constants remain unspecified.',
            'source': source('PAIR-ASYMPTOTIC-001', 'eq:pair-normalization')},
        'substitution': {'identities': ['X=T^a', 'l=a*q'],
                         'negative_alpha': 'Use exact evenness, not a prime estimate at X<1.',
                         'source': source('PAIR-POSITIVITY-001', 'cor:pair-positivity')},
        'final': {'main_terms': [term.record() for term in main],
                  'absolute_error_scales': [term.record() for term in errors],
                  'source': source('PAIR-ASYMPTOTIC-001', 'eq:pair-asymptotic-bound')},
        'endpoints': [
            {'alpha': str(a), 'main_terms': [term.endpoint(a).record() for term in main],
             'absolute_error_scales': [term.endpoint(a).record() for term in errors]}
            for a in (0, 1, -1)],
        'scope': ['Analytic bounds and uniformity are inputs from the written proof.',
                  'Big-O constants are effective but are not computed here.',
                  'At alpha=0 retain the peak error scale 1, giving total error O(1).',
                  'At alpha=+/-1 the written proof absorbs T^(-2)q into O(q^(-1/2)).',
                  'Full complex-zero weights, multiplicities and C_T are unchanged.',
                  'Published computer-assisted dependencies are not replayed.'],
    }


def validate_sources(report, root):
    ledger = (root / 'research/theorem-ledger.yaml').read_text()
    ids = set(re.findall(r'^  - id: ([A-Z0-9-]+)$', ledger, re.M))

    def walk(value):
        if isinstance(value, dict):
            if set(('claim_id', 'file', 'label')) <= value.keys():
                if value['claim_id'] not in ids:
                    raise ValueError(f"unknown source claim: {value['claim_id']}")
                text = (root / value['file']).read_text()
                if '\\label{' + value['label'] + '}' not in text:
                    raise ValueError(f"missing manuscript label: {value['label']}")
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)
    walk(report)


def json_text(report):
    return json.dumps(report, indent=2, sort_keys=True) + '\n'


def markdown(report):
    def expr(terms):
        return ' + '.join(t['expression'] for t in terms if t['coefficient'] != '0') or '0'
    lines = [
        '# Regenerated pair normalization', '',
        'Task: verification/exposition. Assumptions: `UNCONDITIONAL`.',
        'Claim: `PAIR-ASYMPTOTIC-001`, status `proved-draft`.', '',
        'Exact arithmetic regenerates the normalization; analytic bounds remain',
        'inputs from the written proof. This is not a proof certificate.', '',
        'Use `q=log T`, `l=log X`, `a=|alpha|`, `T>=3`, `1<=X<=T`, `a<=1`.',
        'Divide `2 pi Phi` by `T q`, giving `Phi/C_T` with `C_T=T q/(2 pi)`.', '',
        '| Component | Before division | After division | After X=T^a, l=a*q |',
        '| --- | --- | --- | --- |',
    ]
    for row in report['rows']:
        cells = [row['id']] + [row[key]['expression'] for key in
                               ('before_normalization', 'after_normalization', 'after_substitution')]
        lines.append('| ' + ' | '.join(f'`{c}`' for c in cells) + ' |')
    lines += ['', 'Error rows give absolute scales with unspecified constants.',
              'Comparison signs reverse when solving for `2 pi Phi`; their absolute',
              'bounds do not change. For `3<=T<5` use the direct bounded-height argument.', '',
              'Absorb the comparison errors using the generated ratios',
              f"`{report['absorption']['comparison_X_over_comparison_T']['expression']} <= 1` and",
              f"`{report['absorption']['comparison_T_over_mean']['expression']} <= 1`.", '',
              '## Final expression', '',
              f"`F_T(alpha) = {expr(report['final']['main_terms'])}`",
              f"with absolute error `O({expr(report['final']['absolute_error_scales'])})`.", '',
              'Negative alpha uses exact evenness. The separate endpoint values are:', '',
              '| alpha | Main terms | Absolute error scales |', '| --- | --- | --- |']
    for endpoint in report['endpoints']:
        lines.append(f"| {endpoint['alpha']} | `{expr(endpoint['main_terms'])}` | "
                     f"`{expr(endpoint['absolute_error_scales'])}` |")
    lines += ['', '## Scope and sources', '']
    lines += ['- ' + note for note in report['scope']]
    lines += ['', 'Claim IDs and exact manuscript labels for each step are retained in',
              '`pair-normalization.json`. The source proof is `proofs/pair_baseline.tex`.', '']
    return '\n'.join(lines)
