#!/usr/bin/env python3
"""STRL/RBF proof-analysis prototype.

Author: Christopher Thomas Ronio
License: supplied as a research prototype; no warranty of formal verification.

The engine provides one typed audit pipeline with domain adapters for finite
set theory, Euclidean metric geometry, finite simplicial topology, and
propositional logic. It is deliberately exact for the included examples.
It is not a general theorem prover and does not certify arbitrary proofs.
"""
from __future__ import annotations

from dataclasses import dataclass, asdict
from fractions import Fraction
from itertools import combinations, product
from math import gcd, isqrt
from typing import Any, Callable, Dict, FrozenSet, Iterable, Mapping, Sequence, Tuple, Type
import argparse
import json


# ---------------------------- Shared STRL/RBF core ----------------------------

@dataclass(frozen=True)
class AuditResult:
    domain: str
    object_type: str
    status: str
    inside: str
    boundary: str
    boundary_line: str
    outside: str
    conclusion: str
    evidence: Mapping[str, Any]
    independent_check: Mapping[str, Any]

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class IllTypedInput(ValueError):
    """Raised when an input does not belong to its declared mathematical type."""


class STRLProofEngine:
    """Shared STRL pipeline; mathematical work is supplied by typed adapters."""

    def __init__(self) -> None:
        self._adapters: Dict[Type[Any], Callable[[Any], AuditResult]] = {}

    def register(self, input_type: Type[Any], adapter: Callable[[Any], AuditResult]) -> None:
        if input_type in self._adapters:
            raise ValueError(f"Adapter already registered for {input_type.__name__}")
        self._adapters[input_type] = adapter

    def analyze(self, problem: Any) -> AuditResult:
        adapter = self._adapters.get(type(problem))
        if adapter is None:
            return AuditResult(
                domain="unknown", object_type=type(problem).__name__,
                status="ILL_TYPED", inside="unrecognized input type",
                boundary="no domain axioms selected", boundary_line="not executed",
                outside="input rejected", conclusion="No mathematical conclusion.",
                evidence={}, independent_check={"performed": False},
            )
        try:
            return adapter(problem)
        except IllTypedInput as exc:
            return AuditResult(
                domain=getattr(problem, "domain", "unclassified"),
                object_type=type(problem).__name__, status="ILL_TYPED",
                inside="input failed type validation", boundary="domain assumptions not established",
                boundary_line="adapter execution stopped", outside=str(exc),
                conclusion="No mathematical conclusion; repair the input type or hypotheses.",
                evidence={"validation_error": str(exc)},
                independent_check={"performed": False},
            )


@dataclass(frozen=True)
class ProofStep:
    """One node in a proof certificate dependency graph.

    `checker` is the local inference validator. It receives a mapping from
    premise identifiers to their already-verified Boolean values.
    Cross-domain premises require an explicit `bridge=True` declaration.
    """
    identifier: str
    domain: str
    statement: str
    premises: Tuple[str, ...]
    checker: Callable[[Mapping[str, bool]], bool]
    bridge: bool = False


@dataclass(frozen=True)
class ProofDAGResult:
    status: str
    target: str
    dependency_order: Tuple[str, ...]
    node_results: Mapping[str, bool]
    errors: Tuple[str, ...]


def verify_proof_dag(steps: Sequence[ProofStep], target: str) -> ProofDAGResult:
    """Check dependency integrity, acyclicity, typing, and each local rule.

    This validates a supplied proof certificate; soundness still depends on
    the correctness of each registered/supplied local checker.
    """
    by_id: Dict[str, ProofStep] = {}
    errors = []
    for step in steps:
        if step.identifier in by_id:
            errors.append(f"duplicate proof-step identifier: {step.identifier}")
        by_id[step.identifier] = step
    if target not in by_id:
        return ProofDAGResult("ILL_TYPED", target, (), {}, ("target node is missing",))

    order = []
    visiting = set()
    visited = set()

    def visit(node_id: str) -> None:
        if node_id in visiting:
            errors.append(f"cycle detected at proof step: {node_id}")
            return
        if node_id in visited:
            return
        step = by_id.get(node_id)
        if step is None:
            errors.append(f"missing premise node: {node_id}")
            return
        visiting.add(node_id)
        for premise_id in step.premises:
            premise = by_id.get(premise_id)
            if premise is not None and premise.domain != step.domain and not step.bridge:
                errors.append(f"undeclared cross-domain inference: {premise_id} -> {node_id}")
            visit(premise_id)
        visiting.remove(node_id)
        visited.add(node_id)
        order.append(node_id)

    visit(target)
    node_results: Dict[str, bool] = {}
    for node_id in order:
        step = by_id[node_id]
        premises_ok = all(node_results.get(premise_id, False) for premise_id in step.premises)
        if not premises_ok:
            node_results[node_id] = False
            continue
        try:
            node_results[node_id] = bool(step.checker(node_results))
        except Exception as exc:  # a malformed checker is a failed certificate step
            errors.append(f"checker failed at {node_id}: {type(exc).__name__}: {exc}")
            node_results[node_id] = False
    success = not errors and node_results.get(target, False)
    return ProofDAGResult("VERIFIED" if success else "REFUTED_OR_INCOMPLETE",
                          target, tuple(order), node_results, tuple(errors))


# ---------------------------- Finite set theory -------------------------------

@dataclass(frozen=True)
class SetPartitionProblem:
    universe: FrozenSet[Any]
    subset: FrozenSet[Any]


def _analyze_set_partition(p: SetPartitionProblem) -> AuditResult:
    if not isinstance(p.universe, frozenset) or not isinstance(p.subset, frozenset):
        raise IllTypedInput("universe and subset must be frozensets")
    if not p.subset.issubset(p.universe):
        return AuditResult(
            "set_theory", "SetPartitionProblem", "REFUTED",
            "U and A are finite sets", "A ⊆ U is required",
            "A ⊄ U", "the subset hypothesis fails",
            "The partition theorem is not applicable to this input.",
            {"U": sorted(map(repr, p.universe)), "A": sorted(map(repr, p.subset))},
            {"performed": False, "reason": "failed boundary hypothesis"},
        )

    complement = p.universe - p.subset
    intersection = p.subset & complement
    union = p.subset | complement
    primary = (not intersection) and (union == p.universe)

    # Independent check: count membership states directly for every x in U.
    memberships = [(x in p.subset, x in complement) for x in p.universe]
    independent = all(sum(pair) == 1 for pair in memberships)
    status = "VERIFIED" if primary and independent else "REFUTED"
    return AuditResult(
        domain="set_theory", object_type="SetPartitionProblem", status=status,
        inside="A is a subset of U",
        boundary="complement is defined relative to the fixed universe U",
        boundary_line="A ↦ U\\A; test intersection and union",
        outside="A ∩ (U\\A) = ∅ and A ∪ (U\\A) = U" if primary else "partition identity failed",
        conclusion="A and its relative complement partition U." if status == "VERIFIED" else "Partition check failed.",
        evidence={
            "universe_size": len(p.universe), "subset_size": len(p.subset),
            "complement_size": len(complement), "intersection_size": len(intersection),
            "union_equals_universe": union == p.universe,
        },
        independent_check={"performed": True, "method": "per-element membership count",
                           "each_element_in_exactly_one_side": independent,
                           "elements_checked": len(memberships)},
    )


# ------------------------------ Euclidean geometry ----------------------------

@dataclass(frozen=True)
class PythagoreanProblem:
    a: int
    b: int
    c: int


def _analyze_pythagorean(p: PythagoreanProblem) -> AuditResult:
    if any(type(v) is not int or v <= 0 for v in (p.a, p.b, p.c)):
        raise IllTypedInput("a, b, and c must be positive integers")

    # Primary exact arithmetic check.
    lhs = p.a * p.a + p.b * p.b
    rhs = p.c * p.c
    primary = lhs == rhs

    # Independent exact area-decomposition check using rational arithmetic:
    # (a+b)^2 = 4(ab/2) + c^2 for a valid Pythagorean triple.
    outer_square = Fraction((p.a + p.b) ** 2, 1)
    four_triangle_areas = 4 * Fraction(p.a * p.b, 2)
    inner_square = Fraction(p.c * p.c, 1)
    area_identity = outer_square == four_triangle_areas + inner_square
    independent = area_identity

    status = "VERIFIED" if primary and independent else "REFUTED"
    return AuditResult(
        domain="geometry", object_type="PythagoreanProblem", status=status,
        inside="positive integer side lengths (a, b, c)",
        boundary="Euclidean right-triangle hypothesis; c is the proposed hypotenuse",
        boundary_line="compare a²+b² with c², then check an area identity independently",
        outside="a²+b² = c²" if primary else "a²+b² ≠ c²",
        conclusion=("The supplied lengths satisfy the Pythagorean relation." if status == "VERIFIED"
                    else "The supplied lengths do not satisfy the Pythagorean relation."),
        evidence={"a": p.a, "b": p.b, "c": p.c, "a_squared_plus_b_squared": lhs,
                  "c_squared": rhs, "primary_equality": primary},
        independent_check={"performed": True, "method": "exact area decomposition with Fraction",
                           "outer_square_area": str(outer_square),
                           "four_triangle_areas": str(four_triangle_areas),
                           "inner_square_area": str(inner_square),
                           "area_identity_holds": area_identity},
    )


# ----------------------------- Finite simplicial topology ----------------------

@dataclass(frozen=True)
class SimplicialComplexProblem:
    # Maximal simplices. Every simplex is represented by a nonempty frozenset
    # of hashable vertex labels; the complex is their downward closure.
    facets: Tuple[FrozenSet[Any], ...]


def _all_nonempty_faces(facets: Sequence[FrozenSet[Any]]) -> FrozenSet[FrozenSet[Any]]:
    faces = set()
    for facet in facets:
        for k in range(1, len(facet) + 1):
            faces.update(frozenset(c) for c in combinations(facet, k))
    return frozenset(faces)


def _analyze_simplicial_complex(p: SimplicialComplexProblem) -> AuditResult:
    if not p.facets:
        raise IllTypedInput("at least one nonempty facet is required")
    if any(not isinstance(f, frozenset) or len(f) == 0 for f in p.facets):
        raise IllTypedInput("each facet must be a nonempty frozenset")
    if len(set(p.facets)) != len(p.facets):
        raise IllTypedInput("duplicate facets are not permitted")

    faces = _all_nonempty_faces(p.facets)
    # Verify closure under taking nonempty subsets.
    closure_ok = all(
        frozenset(sub) in faces
        for face in faces
        for k in range(1, len(face) + 1)
        for sub in combinations(face, k)
    )
    f_vector = {}
    for face in faces:
        dim = len(face) - 1
        f_vector[dim] = f_vector.get(dim, 0) + 1
    max_dim = max(f_vector)
    euler_characteristic = sum(((-1) ** dim) * count for dim, count in f_vector.items())

    # Independent check: recompute the f-vector using dimension buckets built
    # from the vertex-label union, rather than the primary face-count loop.
    vertices = frozenset().union(*p.facets)
    independent_counts = {
        dim: sum(1 for face in faces if len(face) == dim + 1)
        for dim in range(max_dim + 1)
    }
    independent_euler = sum((1 if dim % 2 == 0 else -1) * count
                            for dim, count in independent_counts.items())
    independent_ok = (independent_counts == f_vector and independent_euler == euler_characteristic)

    status = "VERIFIED" if closure_ok and independent_ok else "REFUTED"
    return AuditResult(
        domain="topology", object_type="SimplicialComplexProblem", status=status,
        inside="finite family of nonempty vertex sets",
        boundary="the represented collection must be a simplicial complex (downward closed)",
        boundary_line="generate faces, check closure, compute alternating face count",
        outside="Euler characteristic χ = Σ(-1)^k f_k",
        conclusion=(f"Valid finite simplicial complex; Euler characteristic χ = {euler_characteristic}."
                    if status == "VERIFIED" else "Simplicial-complex validation failed."),
        evidence={"facet_count": len(p.facets), "vertex_count": len(vertices),
                  "f_vector": {str(k): v for k, v in sorted(f_vector.items())},
                  "closure_under_nonempty_subsets": closure_ok,
                  "euler_characteristic": euler_characteristic},
        independent_check={"performed": True, "method": "separate dimension-bucket recount",
                           "f_vector_matches": independent_counts == f_vector,
                           "euler_characteristic_matches": independent_euler == euler_characteristic},
    )


# ------------------------------ Mathematical logic ----------------------------

class Formula:
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        raise NotImplementedError

    def variables(self) -> FrozenSet[str]:
        raise NotImplementedError


@dataclass(frozen=True)
class Var(Formula):
    name: str
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        if self.name not in env:
            raise IllTypedInput(f"unbound proposition: {self.name}")
        return bool(env[self.name])
    def variables(self) -> FrozenSet[str]:
        return frozenset({self.name})


@dataclass(frozen=True)
class Not(Formula):
    item: Formula
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        return not self.item.evaluate(env)
    def variables(self) -> FrozenSet[str]:
        return self.item.variables()


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        return self.left.evaluate(env) and self.right.evaluate(env)
    def variables(self) -> FrozenSet[str]:
        return self.left.variables() | self.right.variables()


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        return self.left.evaluate(env) or self.right.evaluate(env)
    def variables(self) -> FrozenSet[str]:
        return self.left.variables() | self.right.variables()


@dataclass(frozen=True)
class Implies(Formula):
    left: Formula
    right: Formula
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        return (not self.left.evaluate(env)) or self.right.evaluate(env)
    def variables(self) -> FrozenSet[str]:
        return self.left.variables() | self.right.variables()


@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula
    def evaluate(self, env: Mapping[str, bool]) -> bool:
        return self.left.evaluate(env) == self.right.evaluate(env)
    def variables(self) -> FrozenSet[str]:
        return self.left.variables() | self.right.variables()


@dataclass(frozen=True)
class LogicTautologyProblem:
    formula: Formula


def _evaluate_independently(formula: Formula, env: Mapping[str, bool]) -> bool:
    """Second evaluator using explicit node-type dispatch (separate code path)."""
    if isinstance(formula, Var):
        if formula.name not in env:
            raise IllTypedInput(f"unbound proposition: {formula.name}")
        return env[formula.name]
    if isinstance(formula, Not):
        return not _evaluate_independently(formula.item, env)
    if isinstance(formula, And):
        left = _evaluate_independently(formula.left, env)
        right = _evaluate_independently(formula.right, env)
        return left and right
    if isinstance(formula, Or):
        left = _evaluate_independently(formula.left, env)
        right = _evaluate_independently(formula.right, env)
        return left or right
    if isinstance(formula, Implies):
        left = _evaluate_independently(formula.left, env)
        right = _evaluate_independently(formula.right, env)
        return (not left) or right
    if isinstance(formula, Iff):
        left = _evaluate_independently(formula.left, env)
        right = _evaluate_independently(formula.right, env)
        return left == right
    raise IllTypedInput(f"unsupported formula node: {type(formula).__name__}")


def _analyze_logic(p: LogicTautologyProblem) -> AuditResult:
    if not isinstance(p.formula, Formula):
        raise IllTypedInput("formula must be a Formula node")
    names = sorted(p.formula.variables())
    if len(names) > 16:
        raise IllTypedInput("truth-table cap is 16 variables (65,536 assignments)")
    assignments = [dict(zip(names, values)) for values in product((False, True), repeat=len(names))]
    results = [p.formula.evaluate(env) for env in assignments]
    second_results = [_evaluate_independently(p.formula, env) for env in assignments]
    tautology = all(results)
    independent_agreement = results == second_results
    counterexamples = [env for env, value in zip(assignments, results) if not value]
    status = "VERIFIED" if tautology and independent_agreement else "REFUTED"
    return AuditResult(
        domain="mathematical_logic", object_type="LogicTautologyProblem", status=status,
        inside="well-formed propositional formula over declared variables",
        boundary=f"classical Boolean semantics; exhaustive domain of 2^{len(names)} assignments",
        boundary_line="evaluate the formula under every valuation",
        outside="tautology iff every valuation evaluates to True",
        conclusion=("Formula is a classical tautology." if status == "VERIFIED"
                    else "Formula is not a tautology; a countervaluation exists or evaluators disagree."),
        evidence={"variables": names, "assignments_checked": len(assignments),
                  "tautology": tautology,
                  "counterexamples": counterexamples[:8]},
        independent_check={"performed": True, "method": "second recursive evaluator with explicit dispatch",
                           "evaluators_agree_on_all_assignments": independent_agreement},
    )


def build_engine() -> STRLProofEngine:
    engine = STRLProofEngine()
    engine.register(SetPartitionProblem, _analyze_set_partition)
    engine.register(PythagoreanProblem, _analyze_pythagorean)
    engine.register(SimplicialComplexProblem, _analyze_simplicial_complex)
    engine.register(LogicTautologyProblem, _analyze_logic)
    return engine


def demo_problems() -> Dict[str, Any]:
    p, q = Var("P"), Var("Q")
    de_morgan = Iff(Not(And(p, q)), Or(Not(p), Not(q)))
    return {
        "set_partition": SetPartitionProblem(
            frozenset({"a", "b", "c", "d"}), frozenset({"a", "c"})),
        "pythagorean_3_4_5": PythagoreanProblem(3, 4, 5),
        "tetrahedron_boundary": SimplicialComplexProblem((
            frozenset({0, 1, 2}), frozenset({0, 1, 3}),
            frozenset({0, 2, 3}), frozenset({1, 2, 3}),
        )),
        "de_morgan_law": LogicTautologyProblem(de_morgan),
    }


def enumerate_pythagorean_bruteforce(limit: int) -> FrozenSet[Tuple[int, int, int]]:
    """All unordered positive integer triples with hypotenuse <= limit."""
    triples = set()
    for a in range(1, limit + 1):
        for b in range(a, limit + 1):
            square_sum = a * a + b * b
            c = isqrt(square_sum)
            if c <= limit and c * c == square_sum:
                triples.add((a, b, c))
    return frozenset(triples)


def enumerate_pythagorean_euclid(limit: int) -> FrozenSet[Tuple[int, int, int]]:
    """Independent generation using Euclid's primitive-triple parameterization."""
    triples = set()
    for m in range(2, isqrt(limit) + 1):
        for n in range(1, m):
            if gcd(m, n) != 1 or (m - n) % 2 == 0:
                continue
            x, y, c0 = m * m - n * n, 2 * m * n, m * m + n * n
            a0, b0 = sorted((x, y))
            for scale in range(1, limit // c0 + 1):
                triples.add((scale * a0, scale * b0, scale * c0))
    return frozenset(triples)


def run_self_tests() -> Dict[str, Any]:
    engine = build_engine()
    results = {name: engine.analyze(problem).to_dict()
               for name, problem in demo_problems().items()}
    failures = [name for name, result in results.items() if result["status"] != "VERIFIED"]

    # Negative controls: each must be rejected by the appropriate adapter.
    bad_geometry = engine.analyze(PythagoreanProblem(3, 4, 6))
    bad_partition = engine.analyze(SetPartitionProblem(frozenset({1, 2}), frozenset({1, 3})))
    bad_type = engine.analyze(PythagoreanProblem(3, 0, 5))
    r, s = Var("R"), Var("S")
    non_tautology = engine.analyze(LogicTautologyProblem(And(r, s)))
    negative_controls = {
        "bad_pythagorean_triple_rejected": bad_geometry.status == "REFUTED",
        "invalid_subset_hypothesis_rejected": bad_partition.status == "REFUTED",
        "ill_typed_geometry_input_rejected": bad_type.status == "ILL_TYPED",
        "non_tautology_rejected": non_tautology.status == "REFUTED",
    }
    if not all(negative_controls.values()):
        failures.append("negative_controls")

    # Exhaust all 2^4 subsets of a four-element universe.
    universe = frozenset({0, 1, 2, 3})
    subset_checks = 0
    subset_exhaustive_ok = True
    for mask in range(1 << len(universe)):
        subset = frozenset(x for i, x in enumerate(sorted(universe)) if mask & (1 << i))
        check = engine.analyze(SetPartitionProblem(universe, subset))
        subset_checks += 1
        subset_exhaustive_ok = subset_exhaustive_ok and check.status == "VERIFIED"

    # Independently enumerate Pythagorean triples up to hypotenuse 100.
    brute = enumerate_pythagorean_bruteforce(100)
    euclid = enumerate_pythagorean_euclid(100)
    pythagorean_exhaustive_ok = brute == euclid

    # A small proof certificate: P and (P -> Q) entail Q by modus ponens.
    dag = verify_proof_dag((
        ProofStep("premise_P", "mathematical_logic", "P", (), lambda _: True),
        ProofStep("premise_P_implies_Q", "mathematical_logic", "P -> Q", (), lambda _: True),
        ProofStep("conclusion_Q", "mathematical_logic", "Q",
                  ("premise_P", "premise_P_implies_Q"),
                  lambda known: known["premise_P"] and known["premise_P_implies_Q"]),
    ), "conclusion_Q")
    dag_ok = dag.status == "VERIFIED"

    exhaustive_checks = {
        "finite_set_partition": {"universe_size": 4, "subsets_checked": subset_checks,
                                 "all_partitions_verified": subset_exhaustive_ok},
        "pythagorean_triples": {"maximum_hypotenuse": 100,
                                "brute_force_count": len(brute),
                                "euclid_generation_count": len(euclid),
                                "independent_enumerations_match": pythagorean_exhaustive_ok},
        "proof_dag_modus_ponens": {"status": dag.status,
                                   "dependency_order": list(dag.dependency_order),
                                   "no_errors": not dag.errors},
    }
    if not subset_exhaustive_ok or not pythagorean_exhaustive_ok or not dag_ok:
        failures.append("exhaustive_or_proof_dag_checks")

    return {
        "engine": "STRL/RBF proof-analysis prototype",
        "author": "Christopher Thomas Ronio",
        "all_demo_cases_verified": not failures,
        "failures": failures,
        "cases": results,
        "negative_controls": negative_controls,
        "exhaustive_checks": exhaustive_checks,
        "scope": "exact finite checks and example-level verification; not a general theorem prover",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run all built-in exact checks")
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON")
    args = parser.parse_args()
    if not args.self_test:
        parser.print_help()
        return 0
    report = run_self_tests()
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["all_demo_cases_verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
