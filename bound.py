import enum
import logging
from typing import TypeVar
from typing_extensions import Self

from logic1.atomlib.sympy import Eq, Le, Lt, Ge, Gt
from logic1.firstorder.formula import And, Formula
from logic1.firstorder.quantified import Ex

from .theories.rings import poly, simplify
from .util import closure, conjunctive_core

Atom = Eq | Le | Lt | Gt | Ge


α = TypeVar("α")


class Bound(enum.IntFlag):
    NONE = 0
    LOWER = enum.auto()
    UPPER = enum.auto()
    BOTH = LOWER | UPPER

    @classmethod
    def of(cls, φ: Atom, x: α) -> Self:
        if x not in φ.get_vars().free:
            return Bound.NONE
        elif isinstance(φ, Eq):
            return Bound.BOTH
        elif isinstance(φ, Le | Lt) == poly(φ).coeff_monomial(x) < 0:
            return Bound.LOWER
        else:
            return Bound.UPPER


def remove_unbounded(φ: Formula) -> Formula:
    return simplify(closure(Ex, And(*remove_unbounded_list(conjunctive_core(φ)))))


def remove_unbounded_list(rows: list[Atom]) -> list[Atom]:
    upper = set(
        [x for φ in rows for x in φ.get_vars().free if Bound.of(φ, x) & Bound.UPPER]
    )
    lower = set(
        [x for φ in rows for x in φ.get_vars().free if Bound.of(φ, x) & Bound.LOWER]
    )

    logging.debug("Variables bounded from above are: " + str(upper))
    logging.debug("Variables bounded from below are: " + str(lower))
    keep = upper.intersection(lower)
    logging.debug("Variables to keep are: " + str(keep))
    return [φ for φ in rows if not φ.get_vars().free.difference(keep)]
