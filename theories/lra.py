import logging
from itertools import product

from logic1.atomlib.sympy import BinaryAtomicFormula, Eq, Ge, Gt, Le, Lt, Ne
from logic1.firstorder.formula import And, Formula
from logic1.firstorder.quantified import Ex
from sympy import Symbol

from ..abc.qe import QuantifierElimination as Base
from ..bound import Bound
from ..util import closure
from .rings import make_simplify, poly

Atom = Le | Lt | Ge | Gt | Eq


def combine_op(
    lower: Le | Lt | Eq, upper: Le | Lt | Eq
) -> type[BinaryAtomicFormula]:
    if isinstance(lower, Le) and isinstance(upper, Le):
        return Le
    if isinstance(lower, Lt | Le) and isinstance(upper, Lt | Le):
        return Lt
    if isinstance(lower, Eq):
        return type(upper)
    if isinstance(upper, Eq):
        return type(lower)
    raise NotImplementedError()


class QuantifierElimination(Base[Symbol]):
    def __init__(self):
        super().__init__(make_simplify())

    def qe1p(self, x: Symbol, φ: Formula) -> Formula:
        """
        Assumes that φ is in prenex normal form and in conjunctive normal form.
        """
        if x not in φ.get_vars().free:
            return φ

        rows: list[BinaryAtomicFormula] = list(φ.args) if isinstance(φ, And) else [φ]  # type: ignore

        upper: list[Atom] = []
        lower: list[Atom] = []
        (both, result) = ([], [])

        for row in rows:
            if not isinstance(row, BinaryAtomicFormula):
                raise NotImplementedError("atoms must be binary")
            if row.args[1] != 0:
                raise NotImplementedError("rhs must be zero")
            if isinstance(row, Ne) or isinstance(row, Gt) or isinstance(row, Ge):
                raise NotImplementedError("cannot handle relation " + str(row.func))
            if (
                not isinstance(row, Le)
                and not isinstance(row, Lt)
                and not isinstance(row, Eq)
            ):
                raise NotImplementedError("unknown relation of type " + str(type(φ)))

            b = Bound.of(row, x)
            logging.debug(str(row) + " is " + str(b) + " for " + str(x))
            if not b:
                result.append(row)
            elif b == Bound.UPPER | Bound.LOWER:
                both.append(row)
            else:
                (upper if b == Bound.UPPER else lower).append(row)

        logging.debug(
            "(upper, lower, both, result) = " + str((upper, lower, both, result))
        )

        if not both and (not upper or not lower):
            ...
        elif both:
            # There is at least one equation for x,
            # so we can use it to substitute x in
            # all other rows.
            e = poly(both[0])
            a = e.coeff_monomial(x)
            e = e - (a * x).as_poly()
            for row in lower + upper + both[1:]:
                p = poly(row)
                b = p.coeff_monomial(x)
                p = (p - (b * x).as_poly()) * a
                p = p + (-b * e)
                result.append((row.func)(p.as_expr(), 0))  # type: ignore
        else:
            # Blow up exponentially!
            for (loweri, upperi) in product(lower, upper):
                logging.debug(
                    "Combining lower bound "
                    + str(loweri)
                    + " and upper bound "
                    + str(upperi)
                )
                (lo, uo) = (loweri.func, upperi.func)
                (lp, up) = (poly(loweri), poly(upperi))
                if isinstance(loweri, Ge | Gt):
                    lp *= -1
                    lo = lo.converse_func
                if isinstance(upperi, Ge | Gt):
                    up *= -1
                    uo = uo.converse_func
                
                assert isinstance(lo, Le | Lt | Eq)
                assert isinstance(uo, Le | Lt | Eq)

                (lps, ups) = (
                    lp.mul_ground(up.coeff_monomial(x)),
                    up.mul_ground(abs(lp.coeff_monomial(x))),
                )
                combo = (combine_op(lo, uo))(lps.add(ups).as_expr(), 0)
                logging.debug(combo)
                result.append(combo)

        return And(*result)


qe = QuantifierElimination().qe
