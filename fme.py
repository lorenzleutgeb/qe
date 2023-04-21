from logic1.firstorder.formula import Formula, And
from logic1.firstorder.quantified import Ex
from logic1.atomlib.sympy import (
    BinaryAtomicFormula,
    Eq,
    Ne,
    Gt,
    Lt,
    Ge,
    Le,
)

from itertools import product

from util import no_alternations, is_conjunctive, conjunctive_core, closure
from bound import remove_unbounded_list, bound, Bound
from rings import poly, make_simplify

import logging


simplify_prefer_lt = make_simplify(prefer=Lt)


def applicable(φ: Formula) -> bool:
    """
    Assumes that φ is in prenex normal form.

    Checks whether this formula admits Fourier-Motzkin eliminiation.
    """
    return no_alternations(Ex, φ) and is_conjunctive(φ)


def combine_op(
    lower: BinaryAtomicFormula, upper: BinaryAtomicFormula
) -> type[BinaryAtomicFormula]:
    if isinstance(lower, Le) and isinstance(upper, Le):
        return Le
    if isinstance(lower, Lt) and isinstance(upper, Lt):
        return Lt
    if isinstance(lower, Lt) and isinstance(upper, Le):
        return Lt
    if isinstance(lower, Le) and isinstance(upper, Lt):
        return Lt
    if isinstance(lower, Eq):
        return type(upper)
    if isinstance(upper, Eq):
        return type(lower)
    raise NotImplementedError()


def fme(φ: Formula, x, eliminate_unbounded: bool = True) -> Formula:
    """
    Assumes that φ is in prenex normal form and in conjunctive normal form.
    """
    if x not in φ.get_qvars():
        return φ

    rows = conjunctive_core(φ)

    if eliminate_unbounded:
        rows = remove_unbounded_list(rows)
        if not any([x in row.get_vars().free for row in rows]):
            # x was eliminated because it was not bounded.
            return simplify_prefer_lt(closure(Ex, And(*rows)))

    upper: list[BinaryAtomicFormula] = []
    lower: list[BinaryAtomicFormula] = []
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

        b = bound(row, x)
        logging.debug(str(row) + " is " + str(b) + " for " + str(x))
        if not b:
            result.append(row)
        elif b == Bound.UPPER | Bound.LOWER:
            both.append(row)
        else:
            (upper if b == Bound.UPPER else lower).append(row)

    logging.debug("(upper, lower, both, result) = " + str((upper, lower, both, result)))

    if not both and (not upper or not lower):
        if eliminate_unbounded:
            raise ValueError(
                "expecting all variables to be bounded, but "
                + str(x)
                + " is not bounded"
            )
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
            (lp, up) = (poly(loweri), poly(upperi))
            (lps, ups) = (
                lp.mul_ground(up.coeff_monomial(x)),
                up.mul_ground(abs(lp.coeff_monomial(x))),
            )
            combo = (combine_op(loweri, upperi))(lps.add(ups).as_expr(), 0)
            logging.debug(combo)
            result.append(combo)

    if eliminate_unbounded:
        result = remove_unbounded_list(result)

    return simplify_prefer_lt(closure(Ex, And(*result)))
