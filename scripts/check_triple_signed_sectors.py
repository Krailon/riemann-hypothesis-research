#!/usr/bin/env python3
"""Exact checks of signed sectors, conjugations and boundary incidence.

Task: verification. Assumptions: UNCONDITIONAL for finite algebra;
SYNTHETIC_MODEL for the quartet-symmetric zero fixtures. These checks are
not an analytic proof or numerical certificate. Standard library only.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import re
import unittest

from check_pair_lemma3 import G, occurrences
from check_pair_rh_audit import field, id_list, indexed_blocks
from check_triple_master import zero_factor, multiply, triple_coefficients

ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT/'research/triple-signed-sectors.json'


def apply(matrix, point):
    return tuple(sum(matrix[i][j]*point[j] for j in range(2)) for i in range(2))


def determinant(m):
    return m[0][0]*m[1][1]-m[0][1]*m[1][0]


def inverse(m):
    d = determinant(m)
    return ((Q(m[1][1], d), Q(-m[0][1], d)),
            (Q(-m[1][0], d), Q(m[0][0], d)))


def gauge(point):
    a, b = point
    return max(abs(a), abs(b), abs(a+b))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate(record):
    require(record['schema_version'] == 1, 'schema')
    require(record['assumptions'] == ['UNCONDITIONAL'], 'assumptions')
    require(record['coordinate_order'] == ['xi', 'eta'], 'coordinate order')
    require(record['gauge']['operation'] == 'max_absolute_linear_forms', 'gauge operation')
    require(record['gauge']['linear_forms'] == [[1, 0], [0, 1], [1, 1]], 'gauge forms')
    require(record['gauge']['outer_radius'] == 1, 'outer radius')
    require(record['gauge']['outer_boundary_included'] is False, 'open support')
    sectors = record['sectors']
    require(len(sectors) == 6, 'six sectors')
    require(len({s['id'] for s in sectors}) == 6, 'unique ids')
    seen, rays = set(), Counter()
    for sector in sectors:
        m = sector['matrix']
        require(len(m) == 2 and all(len(row) == 2 for row in m), 'matrix shape')
        require(all(type(v) is int for row in m for v in row), 'integer entries')
        require(type(sector['conjugate']) is bool, 'conjugation flag')
        key = tuple(map(tuple, m))
        require(key not in seen, 'unique maps')
        seen.add(key)
        require(determinant(m) == 1, 'Jacobian one')
        sign = -1 if sector['conjugate'] else 1
        frequencies = {tuple(sign*x for x in row) for row in m}
        frequencies.add(tuple(-sign*(m[0][j]+m[1][j]) for j in range(2)))
        require(frequencies == {(1, 0), (0, 1), (-1, -1)}, 'three frequency forms')
        for e in ((1, 0), (0, 1)):
            rays[apply(m, e)] += 1
    require(rays == Counter({v: 2 for v in ((1, 0), (0, 1), (-1, 1),
                                            (-1, 0), (0, -1), (1, -1))}), 'ray incidence')
    limit = record['limit']
    require(limit['normalization'] == '1/log T', 'normalization')
    require(6*Q(limit['quadrant_origin_coefficient']) == Q(limit['origin_coefficient']) == Q(3, 2),
            'origin mass')
    require(2*Q(limit['quadrant_ray_coefficient']) == Q(limit['line_coefficient']) == Q(3, 2),
            'line mass')
    require(limit['line_directions'] == [[1, 0], [0, 1], [1, -1]], 'line directions')
    require(limit['line_density'] == 'abs(r)', 'line density')
    require(record['boundary_conventions']['extra_half_weights'] is False, 'no half weights')
    return sectors


def toy_s(r):
    """Arbitrary exact values obeying S(-r)=conjugate(S(r))."""
    return G(1+r*r, r*(2+r*r))


def toy_c(a, b):
    return toy_s(a)*toy_s(b)*toy_s(-a-b)


class SignedSectorChecks(unittest.TestCase):
    def setUp(self):
        self.record = json.loads(TABLE.read_text())
        self.sectors = validate(self.record)

    def test_reciprocal_reflection_with_full_zero_occurrences(self):
        zeros = occurrences()
        self.assertEqual(Counter(zeros), Counter((-d, g) for d, g in zeros))
        for base, t in product((Q(1), Q(2), Q(1, 3)), (Q(0), Q(7, 2))):
            # Use X=base^4; reverse the formal log-X phases for X^(-1).
            reciprocal = {(-a, -b): c for (a, b), c in zero_factor(zeros, 1/base, t, 0).items()}
            conjugated = zero_factor(zeros, base, t, 0, conjugated=True)
            self.assertEqual(reciprocal, conjugated)
        # S(1,t) sums all phases at zero; reflection makes it real.
        for t in (Q(0), Q(3), Q(9, 2)):
            total = sum(zero_factor(zeros, Q(1), t, 0).values(), G())
            self.assertEqual(total.imag, 0)

    def test_extended_master_at_bases_below_one(self):
        zeros = occurrences()
        for x, y in ((Q(1, 2), Q(1, 3)), (Q(2), Q(1, 3)), (Q(2), Q(1, 2))):
            t = Q(7, 2)
            direct = multiply(multiply(zero_factor(zeros, x, t, 0),
                                       zero_factor(zeros, y, t, 1)),
                              zero_factor(zeros, x*y, t, 2, conjugated=True))
            self.assertEqual(direct, triple_coefficients(zeros, x, y, t))

    def test_geometry_coverage_support_and_seams(self):
        grid = tuple(Q(k, 3) for k in range(-4, 5))
        for a, b in product(grid, repeat=2):
            closed, interior = 0, 0
            for sector in self.sectors:
                u, v = apply(inverse(sector['matrix']), (a, b))
                closed += int(u >= 0 and v >= 0)
                interior += int(u > 0 and v > 0)
                if u >= 0 and v >= 0:
                    self.assertEqual(gauge((a, b)), u+v)
            seam = a*b*(a+b) == 0
            self.assertEqual(interior, 0 if seam else 1)
            self.assertEqual(closed, 6 if a == b == 0 else 2 if seam else 1)
        for kappa in (Q(1, 100), Q(1, 3), Q(9, 10)):
            for u, v in ((Q(0), Q(0)), (1-kappa, Q(0)), (Q(0), 1-kappa),
                         ((1-kappa)/3, 2*(1-kappa)/3)):
                for s in self.sectors:
                    self.assertLessEqual(gauge(apply(s['matrix'], (u, v))), 1-kappa)
        for vertex in ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)):
            self.assertEqual(gauge(vertex), 1)

    def test_signed_observable_identities_and_seam_reality(self):
        for u, v in product((Q(0), Q(1, 3), Q(2)), repeat=2):
            c = toy_c(u, v)
            for s in self.sectors:
                a, b = apply(s['matrix'], (u, v))
                self.assertEqual(toy_c(a, b), c.conjugate() if s['conjugate'] else c)
            self.assertEqual(c, toy_c(v, u))
        for r in (Q(-2), Q(0), Q(1, 3)):
            for a, b in ((r, 0), (0, r), (r, -r)):
                self.assertEqual(toy_c(a, b).imag, 0)

    def test_complex_negative_sector_test_conjugation(self):
        c = toy_c(Q(1, 3), Q(2, 3))
        for s in self.sectors:
            a, b = apply(s['matrix'], (Q(1, 3), Q(2, 3)))
            phi = G(1+a, 2+b)
            actual = phi*toy_c(a, b)
            if s['conjugate']:
                self.assertEqual(actual, (phi.conjugate()*c).conjugate())
                self.assertNotEqual(actual, (phi*c).conjugate())
            else:
                self.assertEqual(actual, phi*c)

    def test_collected_anchor_majorant_and_chain_rule(self):
        for a, b in product((Q(-2), Q(-1, 3), Q(0), Q(1, 2), Q(2)), repeat=2):
            h = gauge((a, b))
            self.assertEqual(h, (abs(a)+abs(b)+abs(a+b))/2)
            exponents = [a*d2+b*d3+(a+b)*d1
                         for d1, d2, d3 in product((Q(-1, 2), Q(1, 2)), repeat=3)]
            self.assertEqual(max(exponents), h)
        for s in self.sectors:
            m = s['matrix']
            self.assertLessEqual(max(sum(abs(x) for x in row) for row in m), 2)
            for gx, gy in product((Q(-2), Q(0), Q(3)), repeat=2):
                gradient = tuple(gx*m[0][j]+gy*m[1][j] for j in range(2))
                self.assertLessEqual(sum(abs(g) for g in gradient), 2*(abs(gx)+abs(gy)))

    def test_origin_and_line_functional_on_complex_polynomial_traces(self):
        # Finite trace algebra on r in [0,a]; not a claim of smooth-test
        # admissibility for these polynomial models.
        a = Q(1, 4)
        coefficients = (G(2, 1), G(-1, 2), G(3, -4), G(2, 3), G(-5, 1), G(4, -2))
        f0, fx, fy, fxx, fxy, fyy = coefficients
        def ray_integral(v):
            x, y = v
            linear, quadratic = fx*x+fy*y, fxx*x*x+fxy*x*y+fyy*y*y
            return f0*a*a/2+linear*a**3/3+quadratic*a**4/4
        sector_sum = G()
        for s in self.sectors:
            rays = [apply(s['matrix'], e) for e in ((1, 0), (0, 1))]
            value = f0/4+Q(3, 4)*sum((ray_integral(v) for v in rays), G())
            sector_sum += value
        expected = Q(3, 2)*f0
        for direction in self.record['limit']['line_directions']:
            opposite = tuple(-x for x in direction)
            expected += Q(3, 2)*(ray_integral(direction)+ray_integral(opposite))
        self.assertEqual(sector_sum, expected)
        self.assertEqual(6*Q(1, 4), Q(3, 2))
        # All primitive ray columns preserve the coordinate r, even the diagonal.
        for s in self.sectors:
            for e in ((1, 0), (0, 1)):
                self.assertEqual(max(abs(x) for x in apply(s['matrix'], e)), 1)

    def test_crossing_and_interior_support_fixtures(self):
        # Rational boxes locate possible smooth bump supports.
        boxes = [((Q(-1, 4), Q(1, 4)), (Q(-1, 4), Q(1, 4))),
                 ((Q(1, 4), Q(1, 2)), (Q(-1, 16), Q(1, 16))),
                 ((Q(-1, 16), Q(1, 16)), (Q(1, 4), Q(1, 2))),
                 ((Q(1, 4), Q(3, 8)), (Q(-3, 8), Q(-1, 4)))]
        for xinterval, yinterval in boxes:
            self.assertTrue(all(gauge(p) < 1 for p in product(xinterval, yinterval)))
        self.assertLess(boxes[1][1][0], 0)
        self.assertGreater(boxes[1][1][1], 0)
        self.assertLess(boxes[2][0][0], 0)
        self.assertGreater(boxes[2][0][1], 0)
        self.assertLess(sum(p[0] for p in boxes[3]), 0)
        self.assertGreater(sum(p[1] for p in boxes[3]), 0)
        for s in self.sectors:
            # A bump inside this mapped box misses every seam.
            for u, v in product((Q(1, 8), Q(1, 4)), repeat=2):
                a, b = apply(s['matrix'], (u, v))
                self.assertNotEqual(a*b*(a+b), 0)
                self.assertLess(gauge((a, b)), 1)

    def test_table_rejects_wrong_maps_flags_coefficients_and_endpoints(self):
        mutations = []
        r = deepcopy(self.record); r['sectors'][1]['matrix'][1][0] = 1; mutations.append(r)
        r = deepcopy(self.record); r['sectors'][3]['conjugate'] = False; mutations.append(r)
        r = deepcopy(self.record); r['sectors'][1]['matrix'] = r['sectors'][0]['matrix']; mutations.append(r)
        r = deepcopy(self.record); r['gauge']['outer_boundary_included'] = True; mutations.append(r)
        r = deepcopy(self.record); r['limit']['line_coefficient'] = '3/4'; mutations.append(r)
        r = deepcopy(self.record); r['limit']['origin_coefficient'] = '1/4'; mutations.append(r)
        r = deepcopy(self.record); r['limit']['normalization'] = '1'; mutations.append(r)
        r = deepcopy(self.record); r['boundary_conventions']['extra_half_weights'] = True; mutations.append(r)
        for record in mutations:
            with self.assertRaises(ValueError):
                validate(record)

    def test_claims_sources_and_support_conventions(self):
        blocks = indexed_blocks((ROOT/'research/theorem-ledger.yaml').read_text())
        claims = {
            'TRIPLE-SIGNED-SECTORS-001': ('lem:triple-signed-sectors',
                {'TRIPLE-MASTER-001', 'PAIR-COUNT-KERNEL-001'}),
            'TRIPLE-SIGNED-TEST-FUNCTION-001': ('thm:triple-signed-test-function',
                {'TRIPLE-SIGNED-SECTORS-001', 'TRIPLE-QUADRANT-LIMIT-001'})}
        tex = (ROOT/'proofs/triple_explicit_formula.tex').read_text()
        md_path = ROOT/'research/triple-test-functions.md'
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
        self.assertIn('SUPPORT(compact subset of max(abs(xi),abs(eta),abs(xi+eta))<1)',
                      field(blocks['TRIPLE-SIGNED-TEST-FUNCTION-001'], 'assumptions'))
        self.assertIn(self.record['source_claim'], blocks)
        self.assertIn(r'\label{'+self.record['source_label']+'}', tex)
        self.assertTrue((ROOT/self.record['source_file']).is_file())
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', md):
            self.assertTrue((md_path.parent/target).is_file(), target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
