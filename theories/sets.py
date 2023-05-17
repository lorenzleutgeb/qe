"""
>>> from sympy.abc import x, y, z
>>> from logic1.firstorder.quantified import Ex, All
>>> simplify(And(Ne(x, y), Ne(y, z)))
And(Ne(x, y), Ne(y, z))
>>> simplify(And(Ne(x, x), Ne(y, z)))
F
>>> simplify(And(Eq(x, x), Eq(y, y)))
T
>>> simplify(And(Ne(x, y), Ne(y, z), Ne(z, y)))
And(Ne(x, y), Ne(y, z))
"""

from itertools import combinations
from typing import Optional

from logic1.atomlib.sympy import Eq, Ne, C, C_
from logic1.firstorder.formula import And, Formula, Or
from logic1.firstorder.truth import TruthValue, F
from sympy import Symbol

from ..util import conjunctive

from ..abc.qe import QuantifierElimination as Base
from ..simplify import Merge, encode, make_simplify

import logging

logger = logging.getLogger("qe")

Variable = Symbol
CardinalityAtom = C | C_
EqualityAtom = Ne | Eq
Atom = EqualityAtom | CardinalityAtom


def merge(ctx: type[And | Or], φ: Atom, ψ: Atom) -> Optional[Merge | TruthValue]:
    if isinstance(φ, EqualityAtom) and isinstance(ψ, EqualityAtom):
        if φ.args == ψ.args and {φ.func, ψ.func} == {Eq, Ne}:
            return encode(ctx is Or)
    elif isinstance(φ, CardinalityAtom) and isinstance(ψ, CardinalityAtom):
        if isinstance(φ, C) and isinstance(ψ, C):
            if φ.index >= ψ.index:
                return Merge.L if ctx is And else Merge.R
            elif φ.index < ψ.index:
                return Merge.R if ctx is And else Merge.L
        elif isinstance(φ, C_) and isinstance(ψ, C_):
            if φ.index >= ψ.index:
                return Merge.R if ctx is And else Merge.L
            elif φ.index < ψ.index:
                return Merge.L if ctx is And else Merge.R
    return None


def simplify_atom(φ: Atom) -> Atom | TruthValue:
    if isinstance(φ, CardinalityAtom):
        return φ

    (lhs, rhs) = φ.args
    assert isinstance(lhs, Symbol) and isinstance(rhs, Symbol)
    if lhs == rhs:
        return encode(isinstance(φ, Eq))
    elif lhs.compare(rhs) <= 0:
        return φ
    else:
        return φ.func(rhs, lhs)


def cmp(φ: Atom, ψ: Atom) -> int:
    if isinstance(φ, CardinalityAtom) and isinstance(ψ, CardinalityAtom):
        return φ.index - ψ.index
    elif isinstance(φ, EqualityAtom) and isinstance(ψ, EqualityAtom):
        result = φ.args[0].compare(ψ.args[0])
        if result == 0:
            return φ.args[1].compare(ψ.args[1])
        else:
            return result
    else:
        return -1 if isinstance(φ, CardinalityAtom) else 1


simplify = make_simplify(atom=simplify_atom, merge=merge, cmp=cmp)


def eta(k: int, zs: set[Symbol]) -> Formula:
    disj = []
    for choice in combinations(zs, k):
        # All elements that are not in the choice are equal to some element in the choice.
        pick = Or(*(Eq(z, c) for z in zs for c in choice if z not in choice))
        # All elements in the choice are pairwise different.
        different = And(*(Ne(*x) for x in combinations(choice, 2)))
        disj.append(different if pick == F else And(pick, different))
    return Or(*disj)


class QuantifierElimination(Base[Symbol]):
    """Quantifier elimination"""

    def __init__(self):
        super().__init__(simplify=simplify)

    def qe1p(self, x: Symbol, φ: Formula) -> Formula:
        ys: set[Symbol] = set()  # Variables that are   equal to x.
        zs: set[Symbol] = set()  # Variables that are unequal to x.

        for a in conjunctive(φ):
            assert isinstance(a.args[0], Symbol) and isinstance(a.args[1], Symbol)
            (zs if isinstance(a, Ne) else ys).add(a.args[0] if a.args[1] == x else a.args[1])

        if ys:
            x = ys.pop()
            return And(*(tuple(Ne(x, z) for z in zs) + tuple(Eq(x, y) for y in ys)))
        else:
            return Or(*(And(eta(k, zs), C(k + 1)) for k in range(1, len(zs) + 1)))


qe = QuantifierElimination()
