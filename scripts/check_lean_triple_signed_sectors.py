#!/usr/bin/env python3
"""Validate the signed-sector passage's verification boundary; no analytic proof by Python."""
import copy
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = {'reflection': 'pairZeroSeries_reciprocal', 'interchange': 'signed_identity', 'support': 'signed_coefficient_bound', 'conjugation': 'signed_sector_decomposition', 'normalization': 'signed_limit_sector_sum', 'limit': 'signed_compact_limit'}


def read_json(path):
    return json.loads((ROOT / path).read_text())


def validate(inventory, config):
    required_import = 'import HigherCorrelations.TripleSignedAssembly'
    for path in ['lean/HigherCorrelations.lean', 'lean/HigherCorrelations/AxiomReport.lean']:
        if required_import not in (ROOT / path).read_text().splitlines():
            raise ValueError('missing signed import: ' + path)
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
    if config['solution_module'] != 'HigherCorrelations.TripleSignedAssembly':
        raise ValueError('wrong solution')
    challenge = (ROOT / 'lean/VerificationChallenges/TripleSigned.lean').read_text()
    imports = re.findall(r'^import HigherCorrelations\.(\w+)', challenge, re.M)
    if not imports or any(not name.endswith('Definitions') for name in imports):
        raise ValueError('challenge imports a proof module')
    challenge_names = re.findall(r'^theorem (\w+)\b', challenge, re.M)
    if ['HigherCorrelations.' + n for n in challenge_names] != config['theorem_names']:
        raise ValueError('challenge declarations differ')
    for tag, name in CONTROLS.items():
        negative = read_json('lean/VerificationChallenges/triple-signed-sectors-' + tag + '-unfinished.json')
        expected = {**config, 'solution_module': 'VerificationChallenges.TripleSignedUnfinished',
                    'theorem_names': ['HigherCorrelations.' + name]}
        if negative != expected:
            raise ValueError('negative-control drift: ' + tag)


class TripleSignedVerificationTests(unittest.TestCase):
    def setUp(self):
        self.inventory = read_json('research/lean-triple-signed-sectors-inventory.json')
        self.config = read_json('lean/VerificationChallenges/triple-signed-sectors.json')

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
