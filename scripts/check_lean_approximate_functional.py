#!/usr/bin/env python3
"""Check AFE prerequisite coverage and the still-open analytic boundary."""
import copy
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = {
    'inclusive': 'afePolynomial_step', 'reflection': 'afeChi_reflection',
    'remainder-reflection': 'afeRemainder_reflection', 'phase-sign': 'afePhase_conj',
    'phase-norm': 'afePhase_mul_conj', 'moving-cutoff': 'afeTwist_admissible',
    'integrability': 'afeTwist_four_polynomials_integrable',
    'compact': 'afeRemainder_compact_short', 'denominator': 'afe_contour_denominator',
    'parameters': 'afe_contour_parameters',
    'stirling-step': 'afeStirlingStep_bound', 'stirling-series': 'afeStirlingCorrection_bound',
    'gamma-identification': 'afeGamma_stirling_closed', 'gamma-remainder': 'afeGamma_stirling_relative',
    'gamma-phase': 'afeChi_phase_uniform', 'phase-transfer': 'afe_phase_replacement_uniform',
    'mellin-summability': 'afe_laplace_summable_integral_norm',
    'mellin-tail': 'afe_mellin_tail', 'hankel-residue': 'afeHankel_residue_sum',
    'hankel-jump': 'afeHankelPrefactor_jump',
    'hankel-small-circle': 'afeHankel_circle_tendsto_zero',
    'hankel-continuation': 'afeHankel_identity_cutoff',
    'hankel-ray-analytic': 'afeHankel_ray_differentiable',
}


def read_json(path):
    return json.loads((ROOT / path).read_text())


def validate(inventory, config):
    for flag in ['global_uniform_remainder_proved', 'saddle_deformation_proved',
                 'density_hypothesis_proved']:
        if inventory[flag]:
            raise ValueError('unproved analytic conclusion: ' + flag)
    if not inventory['compact_constant_depends_on_upper_height']:
        raise ValueError('bounded-height constant misrepresented as absolute')
    if not inventory['gamma_phase_estimate_proved']:
        raise ValueError('Gamma phase estimate coverage missing')
    if not inventory['hankel_identity_nonreal_proved']:
        raise ValueError('fixed-radius Hankel identity coverage missing')
    found = []
    for module in inventory['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = (ROOT / path).read_text()
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M):
            raise ValueError('unfinished or untrusted solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path,
                          comparator_checked=True)
                     for name in re.findall(r'^theorem ([\w.]+)\b', source, re.M))
    if found != inventory['components']:
        raise ValueError('incomplete public declaration coverage')
    if config['theorem_names'] != [c['declaration'] for c in found]:
        raise ValueError('Comparator coverage differs')
    if config['permitted_axioms'] != ['propext', 'Quot.sound', 'Classical.choice'] or config['enable_nanoda']:
        raise ValueError('changed trust boundary')
    if config['solution_module'] != 'HigherCorrelations.ApproximateFunctionalFoundation':
        raise ValueError('wrong solution')
    challenge = (ROOT / 'lean/VerificationChallenges/ApproximateFunctional.lean').read_text()
    imports = re.findall(r'^import HigherCorrelations\.(\w+)', challenge, re.M)
    if imports != ['ApproximateFunctionalDefinitions']:
        raise ValueError('challenge imports a proof module')
    names = re.findall(r'^theorem ([\w.]+)\b', challenge, re.M)
    if ['HigherCorrelations.' + n for n in names] != config['theorem_names']:
        raise ValueError('challenge declarations differ')
    for tag, name in CONTROLS.items():
        negative = read_json('lean/VerificationChallenges/approximate-functional-' + tag + '-unfinished.json')
        expected = {**config, 'solution_module': 'VerificationChallenges.ApproximateFunctionalUnfinished',
                    'theorem_names': ['HigherCorrelations.' + name]}
        if negative != expected:
            raise ValueError('negative-control drift: ' + tag)


class ApproximateFunctionalTests(unittest.TestCase):
    def setUp(self):
        self.inventory = read_json('research/lean-approximate-functional-inventory.json')
        self.config = read_json('lean/VerificationChallenges/approximate-functional.json')

    def test_complete_scope(self):
        validate(self.inventory, self.config)

    def test_unproved_conclusions_rejected(self):
        for flag in ['global_uniform_remainder_proved', 'saddle_deformation_proved',
                     'density_hypothesis_proved']:
            with self.subTest(flag=flag):
                changed = copy.deepcopy(self.inventory)
                changed[flag] = True
                with self.assertRaises(ValueError):
                    validate(changed, self.config)

    def test_height_dependence_required(self):
        changed = copy.deepcopy(self.inventory)
        changed['compact_constant_depends_on_upper_height'] = False
        with self.assertRaises(ValueError):
            validate(changed, self.config)

    def test_omitted_contract_rejected(self):
        changed = copy.deepcopy(self.config)
        changed['theorem_names'].pop()
        with self.assertRaises(ValueError):
            validate(self.inventory, changed)

    def test_untrusted_axiom_rejected(self):
        changed = copy.deepcopy(self.config)
        changed['permitted_axioms'].append('sorryAx')
        with self.assertRaises(ValueError):
            validate(self.inventory, changed)


if __name__ == '__main__':
    unittest.main()
