from typing import Generic, Optional, TypeVar, Any, TypeGuard

from logic1.firstorder import AtomicFormula
from logic1.firstorder.boolean import And, AndOr, Equivalent, Implies, Not, Or
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import QuantifiedFormula
from logic1.firstorder.truth import F, T, TruthValue

from enum import Enum
from functools import cmp_to_key

from ..util import encode, implies, inv_not, list_isinstance

α = TypeVar("α", bound=AtomicFormula, contravariant=True)
β = TypeVar("β")


class Simplifier(Generic[α, β]):
    class Merge(Enum):
        L = 1
        R = 2

        def __str__(self) -> str:
            return "L" if self is Simplifier.Merge.L else "R"

        def __repr__(self) -> str:
            return self.__str__()

    def atom(self, a: α) -> α | TruthValue:
        return a

    def cmp(self, a: α, b: α) -> int:
        return -1

    def merge(self, ctx: type[And | Or], a: α, b: β) -> Optional[Merge | TruthValue | α]:
        return None

    def guard(self, x: Any) -> TypeGuard[α]:
        return isinstance(x, AtomicFormula)

    def __call__(self, φ: Formula) -> Formula:
        """
        >>> from logic1.firstorder.quantified import Ex, All
        >>> from sympy.abc import x, y
        >>> from logic1.atomlib.sympy import Ne, Eq, Lt, Gt
        >>> s = Simplifier()
        >>> s(Ex(x, And(T, Not(F))))
        T
        >>> s(All(x, Or(F, F)))
        F
        """

        def formula_cmp(φ: Formula, ψ: Formula):
            if isinstance(φ, AtomicFormula) and isinstance(ψ, AtomicFormula):
                # Assumes that both atomic formulae are simplified.
                assert self.guard(φ)
                assert self.guard(ψ)
                return self.cmp(φ, ψ)
            elif isinstance(φ, AtomicFormula) and not isinstance(ψ, AtomicFormula):
                return -1
            elif not isinstance(φ, AtomicFormula) and isinstance(ψ, AtomicFormula):
                return 1
            else:
                return 0

        match φ:
            case Implies(args=(φ, ψ)):  # φ → ψ
                return self(implies(φ, ψ))
            case Equivalent(args=(φ, ψ)):  # φ ↔ ψ
                return self(implies(φ, ψ) & implies(ψ, φ))
            case QuantifiedFormula(var=x, arg=ψ):  # φ = ○x.ψ where ○ is ∀ or ∃
                ψ = self(ψ)
                return ψ if x not in ψ.get_vars().free else φ.func(x, ψ)
            case TruthValue():  # φ = ○ where ○ is ⊤ or ⊥
                return φ
            case AtomicFormula():  # φ is an atom, e.g., s ○ t where ○ is one of >, ≥, <, ≤, =, ≠
                assert self.guard(φ)
                return self.atom(φ)
            case Not(arg=ψ):  # φ = ¬ψ
                match self(ψ):
                    case TruthValue():
                        return encode(ψ is F)
                    case AndOr(args=args, dual_func=dual):
                        # De Morgan's Law
                        return self(dual(*map(inv_not, args)))
                    case Implies(args=(φ, ψ)):
                        # Definition of implication using ¬ and ∨ and De Morgan's Law
                        return self(φ & inv_not(ψ))
                    case Equivalent(args=(φ, ψ)):
                        # Definition of equivalence using ¬ and ∨ and De Morgan's Law
                        return self((φ & inv_not(φ) | (ψ & inv_not(ψ))))
                    case AtomicFormula(args=args, complement_func=complement):
                        # Push negation down into atomic formula.
                        return self(complement(*args))
                    case _:
                        raise NotImplementedError()
            case AndOr(args=args, func=func):  # φ = ψ₁ ○ … ○ ψₙ where ○ is ∧ or ∨
                (id, dual) = (T, F) if func == And else (F, T)
                args = filter(lambda x: x is not id, map(self, args))
                args = list(set(args))  # TODO: Find a better way to get unique elements, if this is too slow.

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
                                merged = self.merge(φ.func, ai, aj)  # type: ignore
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
                                elif merged is Simplifier.Merge.R:
                                    args[i] = None
                                    ai = None
                                    changed = True
                                    break
                                elif merged is Simplifier.Merge.L:
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
