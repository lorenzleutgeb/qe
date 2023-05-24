"""
>>> from sympy.abc import x, y, z
>>> from logic1.firstorder.quantified import Ex, All
>>> s = Simplifier()
>>> s(And(Ne(x, y), Ne(y, z)))
And(Ne(x, y), Ne(y, z))
>>> s(And(Ne(x, x), Ne(y, z)))
F
>>> s(And(Eq(x, x), Eq(y, y)))
T
>>> s(And(Ne(x, y), Ne(y, z), Ne(z, y)))
And(Ne(x, y), Ne(y, z))
"""

from itertools import combinations
from typing import Optional

from logic1.atomlib.sympy import Eq, Ne, C, C_
from logic1.firstorder.formula import And, Formula, Or
from logic1.firstorder.truth import TruthValue, F
from sympy import Symbol

from ..util import conjunctive, encode, tuple_isinstance

from ..abc.qe import QuantifierElimination as QuantifierEliminationBase
from ..abc.simp import Simplifier as SimplifierBase

import logging

logger = logging.getLogger("qe")

Variable = Symbol
CardinalityAtom = C | C_
EqualityAtom = Ne | Eq
Atom = EqualityAtom | CardinalityAtom


class Simplifier(SimplifierBase[Atom, Variable]):
    def merge(self, ctx: type[And | Or], φ: Atom, ψ: Atom) -> Optional[SimplifierBase.Merge | TruthValue]:
        if isinstance(φ, EqualityAtom) and isinstance(ψ, EqualityAtom):
            if φ.args == ψ.args and {φ.func, ψ.func} == {Eq, Ne}:
                return encode(ctx is Or)
        elif isinstance(φ, CardinalityAtom) and isinstance(ψ, CardinalityAtom):
            if isinstance(φ, C) and isinstance(ψ, C):
                if φ.index >= ψ.index:
                    return SimplifierBase.Merge.L if ctx is And else SimplifierBase.Merge.R
                elif φ.index < ψ.index:
                    return SimplifierBase.Merge.R if ctx is And else SimplifierBase.Merge.L
            elif isinstance(φ, C_) and isinstance(ψ, C_):
                if φ.index >= ψ.index:
                    return SimplifierBase.Merge.R if ctx is And else SimplifierBase.Merge.L
                elif φ.index < ψ.index:
                    return SimplifierBase.Merge.L if ctx is And else SimplifierBase.Merge.R
        return None

    def atom(self, φ: Atom) -> Atom | TruthValue:
        if isinstance(φ, CardinalityAtom):
            return φ

        assert isinstance(φ.lhs, Variable) and isinstance(φ.rhs, Variable)
        if φ.lhs == φ.rhs:
            return encode(isinstance(φ, Eq))
        elif φ.lhs.compare(φ.rhs) <= 0:
            return φ
        else:
            return φ.func(φ.rhs, φ.lhs)

    def cmp(self, φ: Atom, ψ: Atom) -> int:
        if isinstance(φ, CardinalityAtom) and isinstance(ψ, CardinalityAtom):
            return φ.index - ψ.index
        elif isinstance(φ, EqualityAtom) and isinstance(ψ, EqualityAtom):
            result = φ.lhs.compare(ψ.lhs)
            if result == 0:
                return φ.rhs.compare(ψ.rhs)
            else:
                return result
        else:
            return -1 if isinstance(φ, CardinalityAtom) else 1


simplify = Simplifier()


class QuantifierElimination(QuantifierEliminationBase[Variable]):
    def __init__(self):
        super().__init__(simplify=simplify)

    def qe1p(self, x: Variable, φ: EqualityAtom) -> Formula:
        ys: set[Variable] = set()  # Variables that are   equal to x.
        zs: set[Variable] = set()  # Variables that are unequal to x.

        conj = conjunctive(φ)
        assert tuple_isinstance(conj, EqualityAtom)
        for a in conj:
            assert isinstance(a.lhs, Variable) and isinstance(a.rhs, Variable)
            (zs if isinstance(a, Ne) else ys).add(a.lhs if a.rhs == x else a.rhs)

        if ys:
            x = ys.pop()
            return And(*(tuple(Ne(x, z) for z in zs) + tuple(Eq(x, y) for y in ys)))
        else:
            return Or(*(And(self.eta(k, zs), C(k + 1)) for k in range(1, len(zs) + 1)))

    def eta(self, k: int, zs: set[Variable]) -> Formula:
        disj = []
        for choice in combinations(zs, k):
            # All elements that are not in the choice are equal to some element in the choice.
            pick = Or(*(Eq(z, c) for z in zs for c in choice if z not in choice))
            # All elements in the choice are pairwise different.
            different = And(*(Ne(*x) for x in combinations(choice, 2)))
            disj.append(different if pick == F else And(pick, different))
        return Or(*disj)


qe = QuantifierElimination()
