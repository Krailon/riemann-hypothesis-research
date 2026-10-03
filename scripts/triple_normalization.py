"""Exact regeneration for the weighted triple theorem.

Task: verification/exposition. Assumptions: UNCONDITIONAL and the recorded
support margin. Analytic estimates are inputs, not proved by this module.
"""
from collections import Counter
from fractions import Fraction as Q
import json
from math import factorial
from pathlib import Path

from pair_normalization import Monomial
from check_pair_rh_audit import field, indexed_blocks, require, unique_object
from check_triple_signed_sectors import apply, validate as validate_sectors

ROOT = Path(__file__).resolve().parents[1]
CLAIM = 'TRIPLE-SMOOTHED-CORRELATION-001'
SUPPORT = 'SUPPORT(h<=1-kappa, 0<kappa<1)'
PROOF = 'proofs/triple_explicit_formula.tex'


def source(claim, label):
    return {'claim_id': claim, 'file': PROOF, 'label': label}


def moment(k):
    # Analytic integral identity is supplied by the boundary proof.
    return Q(factorial(k), 2**(k+1))


def generate(root=ROOT):
    table = json.loads((root/'research/triple-signed-sectors.json').read_text(),
                       object_pairs_hook=unique_object)
    sectors = validate_sectors(table)
    origin, ray = moment(0)**2, moment(0)+moment(1)
    incidences = Counter(apply(s['matrix'], e) for s in sectors
                         for e in ((1, 0), (0, 1)))
    native_origin = len(sectors)*origin
    normalization = 1/native_origin
    rays = [{'direction': list(direction), 'incidence': n,
             'native_density_coefficient': str(n*ray),
             'normalized_density_coefficient': str(normalization*n*ray)}
            for direction, n in sorted(incidences.items())]
    require(all(Q(r['normalized_density_coefficient']) == 1 for r in rays),
            'unequal normalized ray coefficients')
    # Expand the two proved bounds; decay denotes B^(-kappa).
    # Avoid the pair formatter's reserved v symbol (rendered there as T^a).
    m = Monomial.make
    signed = [m(phi_C1=1, **weight, **decay)
              for weight in ({}, {'W_inf': 1}, {'W_1': 1})
              for decay in ({'b': -1}, {'decay': 1, 'L': 3})]
    kernel = [m(phi_L1=1, **weight, decay=1, L=3)
              for weight in ({'W_inf': 1}, {'Wprime_inf': 1})]
    errors = []
    for name, terms, formula in (
        ('E_signed', signed, 'phi_C1*(1+W_inf+W_1)*(b^(-1)+decay*L^3)'),
        ('E_kernel', kernel, 'phi_L1*(W_inf+Wprime_inf)*decay*L^3')):
        errors.append({'id': name, 'formula': formula,
            'before_normalization': [t.record() for t in terms],
            'after_exact_scaling': [t.divide(m(1/normalization)).record() for t in terms],
            'source': source(CLAIM, 'eq:triple-assembled-errors')})
    # Basis names distinguish planar densities from origin and line measures.
    partitions = [
        ('all_equal', 'F(0,0)', {'planar_one': 1}),
        ('12_equal', 'integral F(0,r)*(1-s(r)^2) dr', {'line_eta': 1, 'triangle_eta': -1}),
        ('13_equal', 'integral F(r,0)*(1-s(r)^2) dr', {'line_xi': 1, 'triangle_xi': -1}),
        ('23_equal', 'integral F(r,r)*(1-s(r)^2) dr', {'line_sum': 1, 'triangle_sum': -1}),
        ('all_distinct', 'integral F(u,v)*R3(u,v) du dv',
         {'origin': 1, 'triangle_on_line_eta': -1,
          'triangle_on_line_xi': -1, 'triangle_on_line_sum': -1, 'cycle_overlap': 2})]
    total = Counter()
    for _, _, row in partitions:
        total.update(row)
    native = m(8, T=-1, q=-1)
    assembled = native.divide(m(1/normalization))
    report = {
        'schema_version': 1, 'task': 'verification_and_exposition',
        'claim_id': CLAIM, 'claim_status': 'proved-draft',
        'assumptions': ['UNCONDITIONAL', SUPPORT], 'analytic_proof_certificate': False,
        'definitions': {
            'B': 'T/(2*pi)', 'b': 'log B', 'q': 'log T', 'L': 'log(2T+2)',
            'L_T': 'b/(2*pi)', 'decay': 'B^(-kappa)',
            'phi_C1': 'sup|phi|+sup|partial_xi phi|+sup|partial_eta phi|',
            'phi_L1': 'integral |phi|', 'W_inf': 'sup|omega|',
            'W_1': 'integral |omega_prime|', 'Wprime_inf': 'sup|omega_prime|',
            's(r)': 'sin(pi*r)/(pi*r), s(0)=1',
            'R3': 'det[[1,s(u),s(v)],[s(u),1,s(u-v)],[s(v),s(u-v),1]]'},
        'domain': {'height': 'T>=2*pi*e', 'margin': '0<kappa<1',
            'support': 'max(|xi|,|eta|,|xi+eta|)<=1-kappa',
            'outer_boundary_included': False, 'internal_axes_and_origin_included': True,
            'test': 'phi complex smooth compactly supported; F its entire positive-inverse transform',
            'smoothing': 'omega real nonnegative smooth, compact support in (1,2), integral one'},
        'conventions': {
            'forward': 'exp(-2*pi*i*(u*xi+v*eta))', 'inverse': 'exp(+2*pi*i*(u*xi+v*eta))',
            'pairing': 'bilinear, no conjugation', 'line_measure': 'dr, not arclength',
            'tuples': 'all ordered zero occurrences, both ordinate signs, with multiplicity',
            'equalities': 'equal indices, complex zeros and ordinates are distinct conditions',
            'arguments': ['L_T*(gamma_i2-gamma_i1-i*(delta_i2+delta_i1))',
                          'L_T*(gamma_i3-gamma_i1-i*(delta_i3+delta_i1))'],
            'profile': 'J=pi*(24+d12^2+d13^2+d23^2)/((4+d12^2)*(4+d13^2)*(4+d23^2))',
            'centers': ['gamma_i2-gamma_i1-i*delta_i2', 'gamma_i3-gamma_i1-i*delta_i3', 'i*delta_i1'],
            'differences': 'd_mn=c_m-c_n; delta_i=beta_i-1/2',
            'weight': 'omega(gamma_i1/T), anchor only',
            'limit_order': 'Remove independent zero cutoffs at fixed parameters; then fix test, margin and smoothing before T tends to infinity.',
            'asymptotic': 'additive, including zero main terms; varying families must make both errors vanish'},
        'boundary_assembly': {
            'moments': {str(k): str(moment(k)) for k in range(3)},
            'moment_identity': 'integral_0^infinity s^k exp(-2s) ds=k!/2^(k+1)',
            'quadrant_origin': str(origin), 'quadrant_ray': str(ray),
            'sector_count': len(sectors), 'rays': rays,
            'source': source('TRIPLE-QUADRANT-LIMIT-001', 'eq:triple-quadrant-limit')},
        'normalization': {'native_origin': str(native_origin), 'factor': str(normalization),
            'normalized_origin': str(normalization*native_origin),
            'native_observable_coefficient': native.record(),
            'assembled_observable_coefficient': assembled.record(),
            'source': source(CLAIM, 'eq:triple-assembled-observable')},
        'main_functional': {
            'formula': 'phi(0,0)+integral |r|*(phi(r,0)+phi(0,r)+phi(r,-r)) dr',
            'line_directions': table['limit']['line_directions'],
            'source': source('TRIPLE-MAIN-TERM-COMPARISON-001', 'eq:triple-main-term-comparison')},
        'sine_partitions': [{'id': key, 'physical_pairing': physical, 'fourier_basis': row}
                            for key, physical, row in partitions],
        'sine_fourier': {'sum': dict(sorted(total.items())),
            'basis': {'origin': 'delta_(0,0)', 'planar_one': 'constant planar density 1',
                'line_eta': 'delta(eta)', 'line_xi': 'delta(xi)', 'line_sum': 'delta(xi+eta)',
                'triangle_eta': '(1-|eta|)_+', 'triangle_xi': '(1-|xi|)_+',
                'triangle_sum': '(1-|xi+eta|)_+',
                'triangle_on_line_eta': '(1-|xi|)_+ delta(eta)',
                'triangle_on_line_xi': '(1-|eta|)_+ delta(xi)',
                'triangle_on_line_sum': '(1-|xi|)_+ delta(xi+eta)',
                'cycle_overlap': '(1-max(|xi|,|eta|,|xi+eta|))_+'},
            'planar_cancellation': '1-tau(xi)-tau(eta)-tau(xi+eta)+2*(1-h)_+=0 for h<=1',
            'scope': 'Deterministic benchmark; cancellation at h=1 does not extend zeta support.',
            'source': source('TRIPLE-SINE-MEASURE-001', 'eq:triple-sine-fourier')},
        'critical_parameter_specialization': {
            'scope': 'Kernel parameters delta=0 only; applying to every zero would require RH.',
            'profile_at_zero_gaps_in_units_of_pi': str(Q(24, 4**3)),
            'native_relative_to_1_over_T_LT': '3*b/(2*q)',
            'assembled_relative_to_1_over_T_LT': 'b/q',
            'limits': {'native': str(Q(8)*Q(24, 4**3)/2),
                       'assembled': str(normalization*8*Q(24, 4**3)/2)},
            'source': source('TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001', 'eq:triple-critical-normalization')},
        'errors': errors,
        'error_constant_convention': 'Each inherited absolute bound is multiplied by 2/3 exactly. The final theorem absorbs this factor and the inherited effective unspecified constants into an unspecified absolute C; no numerical C is computed.',
    }
    validate_sources(report, root)
    return report


def validate_sources(report, root=ROOT):
    blocks = indexed_blocks((root/'research/theorem-ledger.yaml').read_text())
    require(report['claim_id'] == CLAIM and report['claim_status'] == field(blocks[CLAIM], 'status'),
            'changed root claim or status')
    require(field(blocks[CLAIM], 'assumptions') == '[UNCONDITIONAL, "'+SUPPORT+'"]',
            'changed theorem support')
    require(report['assumptions'] == ['UNCONDITIONAL', SUPPORT], 'changed report assumptions')
    def visit(value):
        if isinstance(value, dict):
            if 'source' in value:
                s = value['source']
                require(s['claim_id'] in blocks and s['file'] == PROOF, 'unknown source claim/file')
                require('\\label{'+s['label']+'}' in (root/s['file']).read_text(), 'missing manuscript label')
            for child in value.values(): visit(child)
        elif isinstance(value, list):
            for child in value: visit(child)
    visit(report)


def json_text(report):
    return json.dumps(report, indent=2, sort_keys=True)+'\n'


def markdown(report):
    n = report['normalization']; b = report['boundary_assembly']
    lines = ['# Regenerated triple normalization and error accounting', '',
        'Task: verification/exposition. `UNCONDITIONAL` with `'+SUPPORT+'`.',
        'Claim `'+CLAIM+'`, status `proved-draft`. No analytic proof certificate.', '',
        '## Main-term assembly', '',
        f"Quadrant origin: `{b['quadrant_origin']}`; quadrant ray: `{b['quadrant_ray']}`.",
        f"Six sectors give origin `{n['native_origin']}`; shared rays each have two incidences.",
        f"Normalization factor: `{n['factor']}`; final origin: `{n['normalized_origin']}`.",
        'Observable coefficient: `'+n['assembled_observable_coefficient']['expression']+'`.',
        'Main functional: `'+report['main_functional']['formula']+'`.', '',
        '## Five occurrence partitions', '', '| Pattern | Physical pairing | Fourier basis coefficients |', '| --- | --- | --- |']
    for row in report['sine_partitions']:
        lines.append('| '+row['id']+' | `'+row['physical_pairing']+'` | `'+json.dumps(row['fourier_basis'],sort_keys=True)+'` |')
    lines += ['', 'Fourier basis definitions and the exact sum are recorded in the JSON.', '',
              '## Named errors', '']
    for error in report['errors']:
        lines += ['- `'+error['id']+' = '+error['formula']+'`.',
                  '  After exact scaling: `'+ ' + '.join(t['expression'] for t in error['after_exact_scaling'])+'`.']
    lines += ['', report['error_constant_convention'], '', '## Scope and limits', '',
              'The full horizontal profile and complex arguments are retained; all ordered occurrence patterns are included.',
              'Support: `'+report['domain']['support']+'`, `0<kappa<1`; internal axes included, outer boundary excluded.',
              report['conventions']['limit_order'], report['conventions']['asymptotic']+'.',
              'Critical parameter specialization has finite-height factors `3b/(2q)` and `b/q`, with limits `3/2` and `1` respectively.',
              report['critical_parameter_specialization']['scope'], '',
              'Definitions, conventions and source labels are supplied in the JSON. Analytic bounds remain inputs from the written proof.']
    return '\n'.join(lines)+'\n'
