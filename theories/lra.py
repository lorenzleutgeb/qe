import logging
from itertools import product

from logic1.atomlib.sympy import Eq, Ge, Gt, Le, Lt
from logic1.firstorder.formula import And, Formula
from logic1.firstorder.truth import T
from sympy import Symbol

from ..abc.qe import QuantifierElimination as Base
from ..bound import Bound
from ..util import conjunctive
from .rings import Simplifier, poly

Atom = Le | Lt | Ge | Gt | Eq


def combine_op(
    lower: Le | Lt | Eq, upper: Le | Lt | Eq
) -> type[Le | Lt | Eq]:
    if isinstance(lower, Le) and isinstance(upper, Le):
        return Le
    elif isinstance(lower, Lt | Le) and isinstance(upper, Lt | Le):
        return Lt
    elif isinstance(lower, Eq):
        return type(upper)
    elif isinstance(upper, Eq):
        return type(lower)
    else:
        raise NotImplementedError()


class QuantifierElimination(Base[Symbol]):
    def __init__(self):
        super().__init__(simplify=Simplifier())

    def qe1p(self, x: Symbol, φ: Formula) -> Formula:
        if x not in φ.get_vars().free:
            return φ

        upper: list[Atom] = []
        lower: list[Atom] = []
        both: list[Atom] = []

        for row in conjunctive(φ):
            if not isinstance(row, Atom):
                raise NotImplementedError("unknown relation of type " + str(type(row)))
            elif row.args[1] != 0:
                raise NotImplementedError("rhs must be zero")

            b = Bound.of(row, x)
            logging.debug(str(row) + " is " + str(b) + " for " + str(x))
            if b == Bound.BOTH:
                both.append(row)
            else:
                (upper if b == Bound.UPPER else lower).append(row)

        logging.debug(
            "(upper, lower, both) = " + str((upper, lower, both))
        )

        result: list[Atom] = []

        if not both and (not upper or not lower):
            return T
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
                result.append((row.func)(p.as_expr(), 0))
            return And(*result)
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
