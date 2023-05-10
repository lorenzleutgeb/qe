import logging
from enum import Enum
from functools import cmp_to_key, partial
from typing import Callable, Optional, TypeVar

from logic1.atomlib.sympy import AtomicFormula
from logic1.firstorder.boolean import And, AndOr, Equivalent, Implies, Not, Or
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import QuantifiedFormula
from logic1.firstorder.truth import F, T, TruthValue

from .util import encode, implies, inv_not, list_isinstance

logging.basicConfig(level=logging.DEBUG)


Atom = TypeVar("Atom", bound=AtomicFormula)


class Merge(Enum):
    L = 1
    R = 2

    def __str__(self) -> str:
        return "L" if self is Merge.L else "R"

    def __repr__(self) -> str:
        return self.__str__()


MergeFunction = Callable[
    [type[And | Or], Atom, Atom], Optional[Merge | TruthValue | Atom]
]


AtomSimplifier = Callable[[Atom], Atom | TruthValue]


AtomCompararer = Callable[[Atom, Atom], int]


def make_simplify(
    atom: AtomSimplifier = lambda x: x,
    merge: MergeFunction = lambda x, y, z: None,
    cmp: AtomCompararer = lambda x, y: 0,
):
    return partial(simplify, atom=atom, merge=merge, cmp=cmp)


def simplify(
    φ: Formula,
    atom: AtomSimplifier = lambda x: x,
    merge: MergeFunction = lambda x, y, z: None,
    cmp: AtomCompararer = lambda x, y: 0,
) -> Formula:
    """
    >>> from logic1.firstorder.quantified import Ex, All
    >>> from sympy.abc import x, y
    >>> from logic1.atomlib.sympy import Ne, Eq, Lt, Gt
    >>> simplify(Ex(x, And(T, Not(F))))
    T
    >>> simplify(All(x, Or(F, F)))
    F
    """

    def rec(φ: Formula) -> Formula:
        # print("recursing into " + str(φ))
        result = simplify(φ, atom, merge, cmp)
        # print("resulted in " + str(result))
        return result

    def formula_cmp(φ: Formula, ψ: Formula):
        if isinstance(φ, AtomicFormula) and isinstance(ψ, AtomicFormula):
            # Assumes that both atomic formulae are simplified.
            return cmp(φ, ψ)
        elif isinstance(φ, AtomicFormula) and not isinstance(ψ, AtomicFormula):
            return -1
        elif not isinstance(φ, AtomicFormula) and isinstance(ψ, AtomicFormula):
            return 1
        else:
            return 0

    # φ = ○ where ○ is ⊤ or ⊥
    if isinstance(φ, TruthValue):
        return φ

    # φ = s ○ t where ○ is one of >, ≥, <, ≤, =, ≠
    elif isinstance(φ, AtomicFormula):
        return atom(φ)

    # φ = φ' → φ''
    elif isinstance(φ, Implies):
        return rec(implies(*φ.args))

    # φ = φ' ↔ φ''
    elif isinstance(φ, Equivalent):
        return rec(And(implies(*φ.args), implies(*reversed(φ.args))))

    # φ = ○x.ψ where ○ is ∀ or ∃
    elif isinstance(φ, QuantifiedFormula):
        ψ = rec(φ.arg)
        return ψ if φ.var not in ψ.get_vars().free else φ.func(φ.var, ψ)

    # φ = ¬ψ
    elif isinstance(φ, Not):
        ψ = rec(φ.arg)
        if isinstance(ψ, TruthValue):
            return encode(ψ is F)
        elif isinstance(ψ, AndOr):
            # De Morgan's Law
            return rec(ψ.dual_func(*[inv_not(x) for x in ψ.args]))
        elif isinstance(ψ, Implies):
            # Definition of implication using ¬ and ∨ and De Morgan's Law
            return rec(And(ψ.args[0], inv_not(ψ.args[1])))
        elif isinstance(ψ, Equivalent):
            # Definition of euivalence using ¬ and ∨ and De Morgan's Law
            return rec(
                Or(
                    And(ψ.args[0], inv_not(ψ.args[1])),
                    And(ψ.args[1], inv_not(ψ.args[0])),
                )
            )
        elif isinstance(ψ, AtomicFormula):
            # Push negation down into atomic formula.
            return rec(ψ.complement_func(*ψ.args))
        else:
            raise NotImplementedError(
                "unreachable, cannot handle: " + str(ψ) + " " + str(type(ψ))
            )

    # φ = ψ₁ ○ … ○ ψₙ where ○ is ∧ or ∨
    elif isinstance(φ, AndOr):
        (id, dual) = (T, F) if isinstance(φ, And) else (F, T)
        args = list(set(filter(lambda x: x is not id, map(rec, φ.args))))

        if not args:
            return id
        if len(args) == 1:
            return args[0]
        elif dual in args:
            return dual

        # if None in args:
        # raise ValueError("none in args 2")

        # print(str(args))
        if list_isinstance(args, AtomicFormula | None):
            changed = True
            while changed:
                changed = False
                for i in range(len(args)):
                    ai = args[i]
                    if ai is None:
                        continue
                    for j in range(i + 1, len(args)):
                        aj = args[j]
                        if aj is None:
                            continue
                        merged = merge(φ.func, ai, aj)  # type: ignore
                        if merged is None:
                            continue
                        elif isinstance(merged, TruthValue):
                            if merged is dual:
                                return dual
                            else:
                                args[i] = None
                                args[j] = None
                                changed = True
                                break
                        elif merged is Merge.R:
                            args[i] = None
                            ai = None
                            changed = True
                            break
                        elif merged is Merge.L:
                            args[j] = None
                            changed = True
                        elif isinstance(merged, AtomicFormula):
                            args[i] = merged
                            ai = merged
                            args[j] = None
                        else:
                            raise NotImplementedError()
            args = list(filter(lambda x: x is not None, args))

        # if None in args:
        # print("FOUND NONE 2")
        # raise ValueError("none in args 2")
        # print("sorting: " + str(args))
        return φ.func(*sorted(args, key=cmp_to_key(formula_cmp)))  # type: ignore
        # return φ.func(*args)  # type: ignore

    return φ
