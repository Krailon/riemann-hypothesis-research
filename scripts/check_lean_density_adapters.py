#!/usr/bin/env python3
"""Validate the conditional density-adapter verification boundary; no analytic proof by Python."""
import copy
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = {'multiplicity': 'rightDensityCount_card', 'reflection': 'densityWindow_reflection', 'endpoints': 'horizontalDensityInterval_endpoint', 'singleton': 'mem_horizontalDensityInterval_singleton', 'cumulative': 'rightDensityCount_difference', 'boundary': 'horizontalDensityInterval_excludes_boundary', 'double': 'horizontalDensityInterval_twice_right', 'cover': 'densityInterval_dyadic_cover', 'window': 'density_comparable_interval', 'scaled': 'density_scaled_tail_bound', 'frozen': 'density_scaled_tail_frozen'}


def read_json(path):
    return json.loads((ROOT / path).read_text())


def validate(inventory, config):
    if inventory['density_hypothesis_proved'] is not False:
        raise ValueError('the analytic density hypothesis is not proved')
    expected_conditional = ['HigherCorrelations.' + n for n in [
        'density_comparable_interval', 'density_scaled_tail_bound',
        'density_scaled_tail_endpoint', 'density_scaled_tail_frozen']]
    if inventory['conditional_declarations'] != expected_conditional:
        raise ValueError('conditional boundary drift')
    found = []
    for module in inventory['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = (ROOT / path).read_text()
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M):
            raise ValueError('unfinished or untrusted solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path,
                          comparator_checked=True)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    analytic = (ROOT / 'lean/HigherCorrelations/DensityWindowAdapters.lean').read_text()
    for name in expected_conditional:
        header = re.search(r'^theorem ' + name.split('.')[-1] + r'\b(.*?) :=', analytic, re.M | re.S)
        if header is None or '(h : UniformDyadicDensity C T₀)' not in header[1]:
            raise ValueError('missing explicit density hypothesis: ' + name)
    if found != inventory['components']:
        raise ValueError('inventory does not cover every public declaration')
    if config['theorem_names'] != [c['declaration'] for c in found]:
        raise ValueError('Comparator coverage differs')
    if config['permitted_axioms'] != ['propext', 'Quot.sound', 'Classical.choice'] or config['enable_nanoda']:
        raise ValueError('changed trust boundary')
    if config['solution_module'] != 'HigherCorrelations.DensityWindowAdapters':
        raise ValueError('wrong solution')
    challenge = (ROOT / 'lean/VerificationChallenges/DensityAdapters.lean').read_text()
    imports = re.findall(r'^import HigherCorrelations\.(\w+)', challenge, re.M)
    if not imports or any(not name.endswith('Definitions') for name in imports):
        raise ValueError('challenge imports a proof module')
    challenge_names = re.findall(r'^theorem (\w+)\b', challenge, re.M)
    if ['HigherCorrelations.' + n for n in challenge_names] != config['theorem_names']:
        raise ValueError('challenge declarations differ')
    for tag, name in CONTROLS.items():
        negative = read_json('lean/VerificationChallenges/density-adapters-' + tag + '-unfinished.json')
        expected = {**config, 'solution_module': 'VerificationChallenges.DensityAdaptersUnfinished',
                    'theorem_names': ['HigherCorrelations.' + name]}
        if negative != expected:
            raise ValueError('negative-control drift: ' + tag)


class DensityAdaptersVerificationTests(unittest.TestCase):
    def setUp(self):
        self.inventory = read_json('research/lean-density-adapters-inventory.json')
        self.config = read_json('lean/VerificationChallenges/density-adapters.json')

    def test_complete_scope(self):
        validate(self.inventory, self.config)

    def test_unproved_density_cannot_be_promoted(self):
        changed = copy.deepcopy(self.inventory)
        changed['density_hypothesis_proved'] = True
        with self.assertRaises(ValueError):
            validate(changed, self.config)

    def test_conditional_boundary_cannot_be_erased(self):
        changed = copy.deepcopy(self.inventory)
        changed['conditional_declarations'].pop()
        with self.assertRaises(ValueError):
            validate(changed, self.config)

    def test_missing_declaration_rejected(self):
        changed = copy.deepcopy(self.inventory)
        changed['components'].pop()
        with self.assertRaises(ValueError):
            validate(changed, self.config)

    def test_missing_comparator_statement_rejected(self):
        changed = copy.deepcopy(self.config)
        changed['theorem_names'].pop()
        with self.assertRaises(ValueError):
            validate(self.inventory, changed)

    def test_untrusted_axiom_rejected(self):
        changed = copy.deepcopy(self.config)
        changed['permitted_axioms'].append('sorryAx')
        with self.assertRaises(ValueError):
            validate(self.inventory, changed)

    def test_external_kernel_scope_drift_rejected(self):
        changed = copy.deepcopy(self.config)
        changed['enable_nanoda'] = True
        with self.assertRaises(ValueError):
            validate(self.inventory, changed)


if __name__ == '__main__':
    unittest.main()
