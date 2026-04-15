"""Lower semantic benchmarks to VMT text."""

from __future__ import annotations

from dataclasses import dataclass

from .ir import (
    Add,
    And,
    ArrayVar,
    Assignment,
    BenchmarkSpec,
    Eq,
    Expr,
    Ge,
    Gt,
    Implies,
    IntConst,
    Lt,
    ScalarVar,
    Select,
    Sort,
    Store,
    VarRef,
    WitnessVar,
)


@dataclass(frozen=True)
class LoweredBenchmark:
    benchmark_name: str
    vmt_text: str


def lower_benchmark(spec: BenchmarkSpec) -> LoweredBenchmark:
    declarations: list[str] = []
    state_vars = list(spec.program.arrays) + list(spec.program.scalars) + list(spec.program.witnesses)
    for var in state_vars:
        declarations.extend(_declare_state_var(var))

    init_text = _lower_and_block(spec.program.init_constraints)
    transition_case = spec.program.transition_cases[0]
    trans_terms = (transition_case.guard,) + tuple(
        Eq(VarRef(f"{assignment.target}_next"), assignment.expr)
        for assignment in transition_case.assignments
    )
    trans_text = _lower_and_block(trans_terms)
    property_text = _lower_and_block((spec.program.property_spec.body,))

    body = "\n".join(
        declarations
        + [
            "",
            "(define-fun init-conditions () Bool (!",
            f" {init_text}",
            " :init true))",
            "",
            "(define-fun trans-conditions () Bool (!",
            f" {trans_text}",
            " :trans true))",
            "",
            "(define-fun property () Bool (!",
            f" {property_text}",
            " :invar-property 0))",
            "",
        ]
    )
    return LoweredBenchmark(benchmark_name=spec.benchmark_name, vmt_text=body)


def _declare_state_var(var: ArrayVar | ScalarVar | WitnessVar) -> list[str]:
    sort_text = _lower_sort(var.sort)
    return [
        f"(declare-fun {var.name} () {sort_text})",
        f"(declare-fun {var.name}_next () {sort_text})",
        f"(define-fun .{var.name} () {sort_text} (! {var.name} :next {var.name}_next))",
    ]


def _lower_sort(sort: Sort) -> str:
    return sort.value


def _lower_expr(expr: Expr) -> str:
    if isinstance(expr, VarRef):
        return expr.name
    if isinstance(expr, IntConst):
        return str(expr.value)
    if isinstance(expr, Add):
        return f"(+ {_lower_expr(expr.left)} {_lower_expr(expr.right)})"
    if isinstance(expr, Select):
        return f"(select {_lower_expr(expr.array)} {_lower_expr(expr.index)})"
    if isinstance(expr, Store):
        return (
            f"(store {_lower_expr(expr.array)} {_lower_expr(expr.index)} "
            f"{_lower_expr(expr.value)})"
        )
    if isinstance(expr, Eq):
        return f"(= {_lower_expr(expr.left)} {_lower_expr(expr.right)})"
    if isinstance(expr, Lt):
        return f"(< {_lower_expr(expr.left)} {_lower_expr(expr.right)})"
    if isinstance(expr, Ge):
        return f"(>= {_lower_expr(expr.left)} {_lower_expr(expr.right)})"
    if isinstance(expr, Gt):
        return f"(> {_lower_expr(expr.left)} {_lower_expr(expr.right)})"
    if isinstance(expr, And):
        if len(expr.terms) == 1:
            return _lower_expr(expr.terms[0])
        return f"(and {' '.join(_lower_expr(term) for term in expr.terms)})"
    if isinstance(expr, Implies):
        return f"(=> {_lower_expr(expr.antecedent)} {_lower_expr(expr.consequent)})"
    raise TypeError(f"unsupported expression: {type(expr)!r}")


def _lower_and_block(terms: tuple[Expr, ...]) -> str:
    lines = ["(and"]
    for term in terms:
        lines.append(_lower_expr(term))
    lines.append(")")
    return "\n".join(lines)
