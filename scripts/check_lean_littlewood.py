#!/usr/bin/env python3
"""Validate the Littlewood rectangle-counting verification boundary; no analytic proof by Python."""
import copy
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = {'transport': 'littlewoodSegmentLog_exp', 'integrability': 'littlewood_vertical_log_integrable', 'boundary': 'littlewood_boundary_integral', 'argument-principle': 'littlewood_weighted_argument', 'identity': 'littlewood_identity', 'count': 'littlewood_count_of_budget', 'zeta': 'littlewood_zeta_budget_positive_height', 'constant': 'littlewood_constant_boundary', 'multiplicity': 'littlewood_repeated_zero', 'threshold': 'littlewood_count_threshold', 'branch': 'littlewood_boundary_branch_invariant'}


def read_json(path):
    return json.loads((ROOT / path).read_text())


def validate(inventory, config):
    if inventory['density_hypothesis_proved'] or inventory['boundary_zeros_allowed']:
        raise ValueError('density or boundary-zero scope overstated')
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
        raise ValueError('inventory does not cover every public declaration')
    if config['theorem_names'] != [c['declaration'] for c in found]:
        raise ValueError('Comparator coverage differs')
    if config['permitted_axioms'] != ['propext', 'Quot.sound', 'Classical.choice'] or config['enable_nanoda']:
        raise ValueError('changed trust boundary')
    if config['solution_module'] != 'HigherCorrelations.LittlewoodExamples':
        raise ValueError('wrong solution')
    challenge = (ROOT / 'lean/VerificationChallenges/Littlewood.lean').read_text()
    imports = re.findall(r'^import HigherCorrelations\.(\w+)', challenge, re.M)
    if not imports or any(not name.endswith('Definitions') for name in imports):
        raise ValueError('challenge imports a proof module')
    challenge_names = re.findall(r'^theorem ([\w.]+)\b', challenge, re.M)
    if ['HigherCorrelations.' + n for n in challenge_names] != config['theorem_names']:
        raise ValueError('challenge declarations differ')
    for tag, name in CONTROLS.items():
        negative = read_json('lean/VerificationChallenges/littlewood-' + tag + '-unfinished.json')
        expected = {**config, 'solution_module': 'VerificationChallenges.LittlewoodUnfinished',
                    'theorem_names': ['HigherCorrelations.' + name]}
        if negative != expected:
            raise ValueError('negative-control drift: ' + tag)


class LittlewoodVerificationTests(unittest.TestCase):
    def setUp(self):
        self.inventory = read_json('research/lean-littlewood-inventory.json')
        self.config = read_json('lean/VerificationChallenges/littlewood.json')

    def test_complete_scope(self):
        validate(self.inventory, self.config)

    def test_density_not_proved(self):
        changed = copy.deepcopy(self.inventory)
        changed['density_hypothesis_proved'] = True
        with self.assertRaises(ValueError):
            validate(changed, self.config)

    def test_boundary_zero_extension_not_proved(self):
        changed = copy.deepcopy(self.inventory)
        changed['boundary_zeros_allowed'] = True
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
