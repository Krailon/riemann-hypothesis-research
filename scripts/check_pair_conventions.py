#!/usr/bin/env python3
"""Check the recorded pair conventions using standard-library exact arithmetic.

Task: verification. Assumptions: UNCONDITIONAL for algebra.
Rational fixtures represent formal symbols, not approximations to pi or logs.
Finite checks do not prove analytic estimates, support theorems, or RH.
Run directly with python3 -B, or with the existing unittest discovery command.
"""

import ast
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import re
import unittest

from check_pair_lemma3 import G, I
from check_pair_prime_mean import (
    fourth_root, k_hat_truncated_powers, triangle,
)


ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / "research/pair-conventions.json"
BASE = {
    "T", "X", "p", "ell", "c", "ell_X", "b", "d", "alpha", "delta",
    "lambda_n", "lambda_m", "Phi", "i",
}
EXTRA = {
    "fourier": {"domain", "forward_sign", "inverse_sign", "angular_factor"},
    "definition": {"domain", "symbol", "expression"},
    "identity": {"domain", "left", "right"},
    "domain": {"conditions"},
    "interval": {
        "domain", "variable", "lower", "upper", "lower_closed", "upper_closed",
        "role", "zero_at_endpoints",
    },
    "count": {"domain", "symbol", "meaning", "exact_normalization"},
    "requirement": {
        "domain", "function_class", "mere_L1_sufficient",
        "later_support_boundary_extension", "justification",
    },
}
DEFINITION_DOMAINS = {
    "A_T": "pair", "L_T": "spacing", "q_T": "spacing", "C_T": "pair",
    "u": "spacing", "x_diff": "pair", "xi": "spacing",
    "mu_n": "prime", "mu_m": "prime", "delta_sq": "prime",
}
IDENTITY_NAMES = {
    "scale", "ratio", "normalization", "vertical_phase", "horizontal_phase",
    "complex_argument", "complex_evaluation_exponent", "same_exponential_base",
    "observable_normalization", "jacobian", "inverse_fourier_phase",
    "prime_frequency", "bandwidth_square",
}
INTERVAL_DOMAINS = {
    "range.alpha": "pair", "range.xi": "spacing", "range.delta": "meanvalue",
    "support.K": "all", "support.B0": "all", "support.K_delta": "bandwidth",
    "support.B0_delta": "bandwidth", "support.M": "bandwidth",
    "near.frequency": "bandwidth", "near.log": "nearby",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_number(value):
    raise ValueError(f"Non-integer JSON number: {value}")


def read_table(text=None):
    return json.loads(
        TABLE.read_text() if text is None else text,
        object_pairs_hook=unique_object,
        parse_float=reject_number,
        parse_constant=reject_number,
    )


def parse_expression(expression, names):
    require(isinstance(expression, str) and 0 < len(expression) <= 400,
            "Expression must be a short nonempty string")
    try:
        tree = ast.parse(expression, mode="eval")
    except SyntaxError as exc:
        raise ValueError("Malformed arithmetic expression") from exc
    allowed = (
        ast.Expression, ast.Constant, ast.Name, ast.Load, ast.UnaryOp,
        ast.UAdd, ast.USub, ast.BinOp, ast.Add, ast.Sub, ast.Mult, ast.Div,
    )
    for node in ast.walk(tree):
        require(isinstance(node, allowed), "Unsupported expression syntax")
        if isinstance(node, ast.Constant):
            require(type(node.value) is int, "Only integer literals are allowed")
        if isinstance(node, ast.Name):
            require(node.id in names, f"Unknown symbol: {node.id}")
    return tree.body


def evaluate(expression, env):
    """Interpret a restricted AST; never call eval or compile."""
    def visit(node):
        if isinstance(node, ast.Constant):
            return Q(node.value)
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, ast.UnaryOp):
            value = visit(node.operand)
            return -value if isinstance(node.op, ast.USub) else value
        left, right = visit(node.left), visit(node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        return left / right
    return visit(parse_expression(expression, env))


def source_check(source, claim_ids):
    require(isinstance(source, dict) and
            set(source) == {"claim_id", "file", "label"}, "Malformed source")
    require(all(isinstance(x, str) and x for x in source.values()),
            "Source values must be nonempty strings")
    require(source["claim_id"] in claim_ids, "Missing ledger claim")
    path = (ROOT / source["file"]).resolve()
    require(path.is_relative_to(ROOT) and path.is_file(), "Missing local source")
    text = path.read_text()
    label = source["label"]
    if path.suffix == ".tex":
        require("\\label{" + label + "}" in text, "Missing TeX source label")
    else:
        headings = re.findall(r"^#+ (.+)$", text, re.MULTILINE)
        require(label in headings, "Missing Markdown source heading")


def validate_structure(table):
    require(isinstance(table, dict) and set(table) == {
        "schema_version", "task", "assumptions", "symbols", "records",
    }, "Malformed table")
    require(type(table["schema_version"]) is int and table["schema_version"] == 1,
            "Unsupported schema version")
    require(table["task"] == "exposition_and_exact_regression", "Wrong task")
    require(table["assumptions"] == ["UNCONDITIONAL"], "Wrong assumptions")
    require(isinstance(table["symbols"], dict) and set(table["symbols"]) == BASE,
            "Unexpected formal symbols")
    require(all(isinstance(v, str) and v for v in table["symbols"].values()),
            "Missing symbol descriptions")
    require(isinstance(table["records"], list), "Records must be a list")
    # Read only the ledger's stable claim-ID lines, not arbitrary YAML.
    ledger_claims = (ROOT / "research/theorem-ledger.yaml").read_text().split(
        "\nclaims:\n", 1
    )[1]
    claim_ids = set(re.findall(r"^  - id: (\S+)$", ledger_claims, re.MULTILINE))
    records = {}
    names = BASE | {"forward_sign", "inverse_sign", "angular_factor"}
    for row in table["records"]:
        require(isinstance(row, dict), "Record must be an object")
        kind = row.get("kind")
        require(kind in EXTRA, "Unknown record kind")
        require(set(row) == {"id", "kind", "source"} | EXTRA[kind],
                "Missing or unexpected record fields")
        key = row["id"]
        require(isinstance(key, str) and key, "Missing record ID")
        require(key not in records, f"Duplicate record ID: {key}")
        records[key] = row
        source_check(row["source"], claim_ids)
        if kind == "domain":
            require(isinstance(row["conditions"], list), "Malformed conditions")
            for rule in row["conditions"]:
                require(isinstance(rule, dict) and
                        set(rule) == {"left", "relation", "right"},
                        "Malformed condition")
                require(rule["relation"] in {">", ">=", "<", "<=", "=="},
                        "Unsupported comparison")
                parse_expression(rule["left"], BASE)
                parse_expression(rule["right"], BASE)
        elif kind == "definition":
            require(isinstance(row["symbol"], str) and row["symbol"] not in names,
                    "Duplicate or missing definition symbol")
            parse_expression(row["expression"], names)
            names = names | {row["symbol"]}
        elif kind == "fourier":
            require(type(row["forward_sign"]) is int and
                    type(row["inverse_sign"]) is int, "Non-integer Fourier sign")
            parse_expression(row["angular_factor"], BASE)
        elif kind == "identity":
            parse_expression(row["left"], names)
            parse_expression(row["right"], names)
        elif kind == "interval":
            for field in ("lower", "upper"):
                parse_expression(row[field], names)
            require(type(row["lower_closed"]) is bool and
                    type(row["upper_closed"]) is bool, "Non-boolean endpoint flag")
            require(row["zero_at_endpoints"] is None or
                    type(row["zero_at_endpoints"]) is bool, "Invalid vanishing flag")
            require(isinstance(row["variable"], str) and row["variable"],
                    "Missing interval variable")
        elif kind == "count":
            require(row["symbol"] == "N_T" and row["meaning"] and
                    row["exact_normalization"] is False, "Zero-count normalization changed")
        elif kind == "requirement":
            require(row["function_class"] == "C_c_infinity(R)" and
                    row["mere_L1_sufficient"] is False and
                    row["later_support_boundary_extension"] is False and
                    isinstance(row["justification"], str) and row["justification"],
                    "Complex-evaluation requirements changed")
    domains = {"all", "pair", "spacing", "meanvalue", "prime", "bandwidth", "nearby"}
    expected = domains | {"fourier", "zero_count", "complex_test_function"}
    expected |= {"def." + n for n in DEFINITION_DOMAINS}
    expected |= {"identity." + n for n in IDENTITY_NAMES}
    expected |= set(INTERVAL_DOMAINS)
    require(set(records) == expected, "Missing or unexpected convention records")
    for key, row in records.items():
        if key in domains:
            require(row["kind"] == "domain", "Wrong domain record kind")
        else:
            require(row.get("domain") in domains, "Missing or unknown domain")
        if key.startswith("def."):
            require(row["kind"] == "definition" and
                    row["symbol"] == key[4:] and
                    row["domain"] == DEFINITION_DOMAINS[key[4:]], "Wrong definition scope")
        elif key.startswith("identity."):
            domain = "prime" if key in {
                "identity.prime_frequency", "identity.bandwidth_square",
            } else "spacing"
            require(row["kind"] == "identity" and row["domain"] == domain,
                    "Wrong identity scope")
        elif key in INTERVAL_DOMAINS:
            require(row["kind"] == "interval" and
                    row["domain"] == INTERVAL_DOMAINS[key], "Wrong interval scope")
    require(records["fourier"]["domain"] == "all", "Wrong Fourier scope")
    require(records["zero_count"]["domain"] == "pair", "Wrong count scope")
    require(records["complex_test_function"]["domain"] == "spacing",
            "Wrong complex-evaluation scope")
    return records


def environment(records, **overrides):
    env = dict(T=Q(16), X=Q(4), p=Q(7), ell=Q(5), c=Q(2),
               ell_X=Q(2), b=Q(1, 4), d=Q(2), alpha=Q(1, 3),
               delta=Q(1, 4), lambda_n=Q(3), lambda_m=Q(1),
               Phi=Q(11), i=I)
    env.update(overrides)
    row = records["fourier"]
    env.update(forward_sign=Q(row["forward_sign"]),
               inverse_sign=Q(row["inverse_sign"]),
               angular_factor=evaluate(row["angular_factor"], env))
    # Ordered definitions permit earlier symbols, never forward references.
    for row in records.values():
        if row["kind"] == "definition":
            env[row["symbol"]] = evaluate(row["expression"], env)
    return env


def in_domain(records, key, env):
    def compare(rule):
        left, right = evaluate(rule["left"], env), evaluate(rule["right"], env)
        relation = rule["relation"]
        if relation == ">":
            return left > right
        if relation == ">=":
            return left >= right
        if relation == "<":
            return left < right
        if relation == "<=":
            return left <= right
        return left == right
    return all(compare(rule) for rule in records[key]["conditions"])


def in_interval(row, value, env):
    lo, hi = evaluate(row["lower"], env), evaluate(row["upper"], env)
    return ((value >= lo if row["lower_closed"] else value > lo) and
            (value <= hi if row["upper_closed"] else value < hi))


def check_algebra(records):
    row = records["fourier"]
    require((row["forward_sign"], row["inverse_sign"]) == (-1, 1),
            "Fourier sign convention changed")
    for p, ell, c in ((Q(7), Q(5), Q(2)), (Q(9, 2), Q(7, 2), Q(1, 2))):
        for alpha, b, d in product(
            (Q(-1), Q(-1, 3), Q(0), Q(1, 3), Q(1)),
            (Q(-1, 4), Q(0), Q(1, 4)), (Q(-2), Q(0), Q(2)),
        ):
            env = environment(records, p=p, ell=ell, c=c, alpha=alpha, b=b, d=d)
            # Independent reference definitions guard against two matching
            # but jointly incorrect sides of an identity.
            expected = {
                "angular_factor": p, "A_T": ell/p, "L_T": (ell-c)/p,
                "q_T": ell/(ell-c), "C_T": env["T"]*ell/p,
                "u": -(ell-c)*d/p, "x_diff": b*ell,
                "xi": alpha*ell/(ell-c), "mu_n": -env["lambda_n"]/p,
                "mu_m": -env["lambda_m"]/p,
                "delta_sq": env["ell_X"]/(4*env["T"]*env["X"]),
            }
            require(all(env[k] == v for k, v in expected.items()),
                    "Scale, orientation, or frequency definition changed")
            require(env["C_T"] != env["T"]*env["L_T"],
                    "Two height normalizations were conflated")
            for row in records.values():
                if row["kind"] == "identity":
                    require(in_domain(records, row["domain"], env), "Fixture outside domain")
                    require(evaluate(row["left"], env) == evaluate(row["right"], env),
                            f"Identity failed: {row['id']}")


def check_boundaries(records):
    env = environment(records)
    # p is a formal positive threshold; this tests T>2*pi without rounding pi.
    for key, cases in {
        "pair": [(Q(3)-Q(1, 100), False), (Q(3), True)],
        "spacing": [(env["p"]-Q(1, 100), False), (env["p"], False),
                    (env["p"]+Q(1, 100), True)],
        "meanvalue": [(Q(1)-Q(1, 100), False), (Q(1), True)],
    }.items():
        for height, expected in cases:
            require(in_domain(records, key, dict(env, T=height)) == expected,
                    f"Height endpoint changed: {key}")
    for height, x, expected in (
        (Q(3), Q(1), True), (Q(3), Q(3), True),
        (Q(3), Q(0), False), (Q(3), Q(4), False), (Q(2), Q(1), False),
    ):
        require(in_domain(records, "prime", dict(env, T=height, X=x)) == expected,
                "Prime-side domain changed")
    require(in_domain(records, "all", env), "Unrestricted convention domain changed")
    expectations = {
        "range.alpha": (-Q(1), Q(1), True, "theorem_frequency", "alpha"),
        "range.xi": (-env["q_T"], env["q_T"], True, "translated_frequency", "xi"),
        "range.delta": (1/(2*env["T"]), Q(1, 2), True, "auxiliary_bandwidth", "delta"),
        "support.K": (-Q(1), Q(1), True, "kernel_support", "frequency"),
        "support.B0": (-Q(1, 2), Q(1, 2), True, "kernel_support", "frequency"),
        "support.K_delta": (-env["delta"], env["delta"], True, "kernel_support", "frequency"),
        "support.B0_delta": (-env["delta"]/2, env["delta"]/2, True, "kernel_support", "frequency"),
        "support.M": (-env["delta"], env["delta"], True, "kernel_support", "frequency"),
        "near.frequency": (Q(0), env["delta"], False, "nearby_pair", "abs_frequency_difference"),
        "near.log": (Q(0), env["p"]*env["delta"], False, "nearby_pair", "abs_log_ratio"),
    }
    for key, (lo, hi, closed, role, variable) in expectations.items():
        row = records[key]
        require((evaluate(row["lower"], env), evaluate(row["upper"], env)) == (lo, hi),
                f"Interval bounds changed: {key}")
        require(row["role"] == role and row["variable"] == variable,
                f"Interval meaning changed: {key}")
        require(row["zero_at_endpoints"] is (True if role == "kernel_support" else None),
                f"Support boundary vanishing changed: {key}")
        step = (hi-lo)/100
        for point, expected in (
            (lo-step, False), (lo, closed), (lo+step, True),
            (hi-step, True), (hi, closed), (hi+step, False),
        ):
            require(in_interval(row, point, env) == expected, f"Endpoint changed: {key}")
    for alpha in (Q(-101, 100), Q(-1), Q(0), Q(1), Q(101, 100)):
        require(in_interval(records["range.alpha"], alpha, env) ==
                in_interval(records["range.xi"], env["q_T"]*alpha, env),
                "Frequency-interval translation failed")
    for delta in (Q(0), 1/(2*env["T"])-Q(1, 1000),
                  1/(2*env["T"]), Q(1, 2), Q(51, 100)):
        e = dict(env, delta=delta)
        require(in_domain(records, "bandwidth", e) ==
                (1/(2*env["T"]) <= delta <= Q(1, 2)), "Bandwidth domain changed")
        require(in_domain(records, "nearby", e) == (0 < delta <= Q(1, 2)),
                "Nearby-pair domain changed")
    require(not in_domain(records, "nearby", dict(env, X=Q(0))),
            "Nearby-pair X domain changed")
    for ratio in (Q(0), Q(99, 100), Q(1), Q(101, 100)):
        gap = env["delta"]*ratio
        require(in_interval(records["near.frequency"], gap, env) ==
                in_interval(records["near.log"], env["p"]*gap, env),
                "Strict nearby-frequency translation failed")


def check_kernels(records):
    env = environment(records)
    for key in ("support.K", "support.K_delta"):
        row = records[key]
        scale = Q(1) if key == "support.K" else env["delta"]
        radius = evaluate(row["upper"], env)
        for sign in (-1, 1):
            require(k_hat_truncated_powers(sign*radius/scale) == 0,
                    "K transform does not vanish at recorded endpoint")
            require(k_hat_truncated_powers(sign*(radius/scale+Q(1, 4))) == 0,
                    "K transform does not vanish outside recorded support")
            require(k_hat_truncated_powers(sign*(radius/scale-Q(1, 4))) > 0,
                    "K support interior fixture vanished")
    for key in ("support.B0", "support.B0_delta"):
        row = records[key]
        scale = Q(1) if key == "support.B0" else env["delta"]
        radius = evaluate(row["upper"], env)/scale
        for frequency in (-radius-Q(1, 4), -radius, -Q(1, 4),
                          Q(1, 4), radius, radius+Q(1, 4)):
            j = 4*frequency
            require(j.denominator == 1, "B0 fixture is not a quarter frequency")
            value = 2*(G(1)+fourth_root(-int(j)))*triangle(2*frequency)
            require((value == G()) == (abs(frequency) >= radius),
                    "B0 support or endpoint value changed")
    # M contains chi*K_delta and translated B0_delta terms. Multiplication
    # by chi-hat or a translation phase cannot enlarge either support.
    m_radius = evaluate(records["support.M"]["upper"], env)
    require(evaluate(records["support.K_delta"]["upper"], env) == m_radius and
            evaluate(records["support.B0_delta"]["upper"], env) < m_radius,
            "M support is inconsistent with its components")


def validate(table):
    records = validate_structure(table)
    check_algebra(records)
    check_boundaries(records)
    check_kernels(records)
    return records


class PairConventions(unittest.TestCase):
    def setUp(self):
        self.table = read_table()

    def test_table_sources_and_schema(self):
        self.assertEqual(len(validate_structure(self.table)), 43)

    def test_exact_scale_phase_and_normalization_identities(self):
        check_algebra(validate_structure(self.table))

    def test_domains_interval_translation_and_endpoints(self):
        check_boundaries(validate_structure(self.table))

    def test_kernel_support_values(self):
        check_kernels(validate_structure(self.table))

    def test_restricted_parser(self):
        self.assertEqual(evaluate("-(x-1)/2", {"x": Q(4)}), Q(-3, 2))
        self.assertEqual(evaluate("i*i", {"i": I}), G(-1))
        for expression in (
            "__import__('os')", "x.real", "x[0]", "2**3", "1//2",
            "1.5", "True", "'text'", "[1]", "unknown", "1 < 2", "x+",
        ):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                evaluate(expression, {"x": Q(4)})

    def test_reject_duplicate_json_keys_and_nonexact_numbers(self):
        for text in ('{"x":1,"x":2}', '{"x":0.5}', '{"x":NaN}'):
            with self.assertRaises(ValueError):
                read_table(text)

    def test_reject_malformed_records_and_sources(self):
        for change in (
            lambda t: t["records"].append(deepcopy(t["records"][0])),
            lambda t: t["records"][0].pop("source"),
            lambda t: t["records"][0]["source"].update(label="absent-label"),
            lambda t: t["records"][0]["source"].update(claim_id="MISSING-001"),
            lambda t: t["records"][0].update(kind="unknown"),
            lambda t: t["records"][-1].update(mere_L1_sufficient=True),
        ):
            bad = deepcopy(self.table)
            change(bad)
            with self.assertRaises(ValueError):
                validate(bad)

    def test_reject_changed_conventions(self):
        for key, field, value in (
            ("fourier", "forward_sign", 1),
            ("fourier", "inverse_sign", -1),
            ("fourier", "angular_factor", "p/2"),
            ("def.C_T", "expression", "T*L_T"),
            ("def.q_T", "expression", "1"),
            ("def.u", "expression", "L_T*d"),
            ("identity.jacobian", "right", "ell/(ell-c)"),
            ("range.alpha", "upper_closed", False),
            ("range.xi", "upper", "1"),
            ("near.frequency", "upper_closed", True),
            ("support.M", "zero_at_endpoints", False),
            ("zero_count", "exact_normalization", True),
            ("complex_test_function", "later_support_boundary_extension", True),
        ):
            with self.subTest(record=key, field=field):
                bad = deepcopy(self.table)
                row = next(r for r in bad["records"] if r["id"] == key)
                row[field] = value
                with self.assertRaises(ValueError):
                    validate(bad)

    def test_reject_changed_height_and_bandwidth_conditions(self):
        for key, index, field, value in (
            ("spacing", 0, "relation", ">="),
            ("pair", 0, "relation", ">"),
            ("meanvalue", 0, "right", "3"),
            ("prime", 2, "relation", "<"),
            ("bandwidth", 1, "relation", ">"),
            ("nearby", 1, "relation", ">="),
        ):
            with self.subTest(domain=key):
                bad = deepcopy(self.table)
                row = next(r for r in bad["records"] if r["id"] == key)
                row["conditions"][index][field] = value
                with self.assertRaises(ValueError):
                    validate(bad)


if __name__ == "__main__":
    unittest.main(verbosity=2)
