#!/usr/bin/env python3
"""Validate the decaying resonance bound's verification boundary; no analytic proof by Python."""
import copy
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = {'count': 'tripleProperPower_count', 'summability': 'tripleResonanceBall_double_summable', 'decay': 'triplePrimeResonantMass_decay'}


def read_json(path):
    return json.loads((ROOT / path).read_text())


def validate(inventory, config):
    found = []
    for module in inventory['modules']:
        path = 'lean/HigherCorrelations/' + module + '.lean'
        source = (ROOT / path).read_text()
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|constant)\b', source, re.M):
            raise ValueError('unfinished or untrusted solution: ' + path)
        found.extend(dict(declaration='HigherCorrelations.' + name, source=path,
                          comparator_checked=True)
                     for name in re.findall(r'^theorem (\w+)\b', source, re.M))
    if found != inventory['components']:
        raise ValueError('inventory does not cover every public declaration')
    if config['theorem_names'] != [c['declaration'] for c in found]:
        raise ValueError('Comparator coverage differs')
    if config['permitted_axioms'] != ['propext', 'Quot.sound', 'Classical.choice'] or config['enable_nanoda']:
        raise ValueError('changed trust boundary')
    if config['solution_module'] != 'HigherCorrelations.TripleResonanceEndpoints':
        raise ValueError('wrong solution')
    challenge = (ROOT / 'lean/VerificationChallenges/TripleResonanceDecay.lean').read_text()
    imports = re.findall(r'^import HigherCorrelations\.(\w+)', challenge, re.M)
    if not imports or any(not name.endswith('Definitions') for name in imports):
        raise ValueError('challenge imports a proof module')
    challenge_names = re.findall(r'^theorem (\w+)\b', challenge, re.M)
    if ['HigherCorrelations.' + n for n in challenge_names] != config['theorem_names']:
        raise ValueError('challenge declarations differ')
    for tag, name in CONTROLS.items():
        negative = read_json('lean/VerificationChallenges/triple-resonance-decay-' + tag + '-unfinished.json')
        expected = {**config, 'solution_module': 'VerificationChallenges.TripleResonanceDecayUnfinished',
                    'theorem_names': ['HigherCorrelations.' + name]}
        if negative != expected:
            raise ValueError('negative-control drift: ' + tag)


class TripleResonanceDecayVerificationTests(unittest.TestCase):
    def setUp(self):
        self.inventory = read_json('research/lean-triple-resonance-decay-inventory.json')
        self.config = read_json('lean/VerificationChallenges/triple-resonance-decay.json')

    def test_complete_scope(self):
        validate(self.inventory, self.config)

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
