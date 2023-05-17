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

    match φ:
        case Implies(args=(φ, ψ)):  # φ → ψ
            return rec(implies(φ, ψ))
        case Equivalent(args=(φ, ψ)):  # φ ↔ ψ
            return rec(And(implies(φ, ψ), implies(ψ, φ)))
        case QuantifiedFormula(var=x, arg=ψ):  # φ = ○x.ψ where ○ is ∀ or ∃
            ψ = rec(ψ)
            return ψ if x not in ψ.get_vars().free else φ.func(x, ψ)
        case TruthValue():  # φ = ○ where ○ is ⊤ or ⊥
            return φ
        case AtomicFormula():  # φ is an atom, e.g., s ○ t where ○ is one of >, ≥, <, ≤, =, ≠
            return atom(φ)
        case Not(arg=ψ):  # φ = ¬ψ
            match rec(ψ):
                case TruthValue():
                    return encode(ψ is F)
                case AndOr(args=args, dual_func=dual):
                    # De Morgan's Law
                    return rec(dual(*map(inv_not, args)))
                case Implies(args=(φ, ψ)):
                    # Definition of implication using ¬ and ∨ and De Morgan's Law
                    return rec(And(φ, inv_not(ψ)))
                case Equivalent(args=(φ, ψ)):
                    # Definition of equivalence using ¬ and ∨ and De Morgan's Law
                    return rec(Or(And(φ, inv_not(φ)), And(ψ, inv_not(ψ))))
                case AtomicFormula(args=args, complement_func=complement):
                    # Push negation down into atomic formula.
                    return rec(complement(*args))
                case _:
                    raise NotImplementedError()
        case AndOr(args=args, func=func):  # φ = ψ₁ ○ … ○ ψₙ where ○ is ∧ or ∨
            (id, dual) = (T, F) if func == And else (F, T)
            args = list(set(filter(lambda x: x is not id, map(rec, args))))

            if not args:
                return id
            if len(args) == 1:
                return args[0]
            elif dual in args:
                return dual

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

            return func(*sorted(args, key=cmp_to_key(formula_cmp)))  # type: ignore

    return φ
