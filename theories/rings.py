"""
>>> from logic1.firstorder.quantified import All, Ex
>>> from logic1.firstorder.boolean import Not, Equivalent, Implies
>>> from logic1.firstorder.truth import F
>>> from sympy.abc import x, y
>>> s = Simplifier()
>>> s(Eq(x - 2, x - 2))
T
>>> s(And(Ge(x, 0), Ne(x, 0)))
Gt(x, 0)
>>> s(Not(Le(x - 1, 0)))
Gt(x - 1, 0)
>>> s(Implies(Lt(x, 1), Le(x, 1)))
T
>>> s(Ex(x, And(T, Not(F))))
T
>>> s(All(x, Or(F, F)))
F
>>> s(Eq(x, 1))
Eq(x - 1, 0)
>>> s(Eq(1, x))
Eq(x - 1, 0)
>>> s(Ne(-1, x))
Ne(x + 1, 0)
>>> s(Eq(-1, x))
Eq(x + 1, 0)
>>> s(Lt(x, 0))
Lt(x, 0)
>>> s(Lt(x, 0))
Lt(x, 0)
>>> s(Lt(-x, 0))
Gt(x, 0)
>>> s(Ex(y, Ex(x, And(Eq(x * x, 0), Eq(y ** 3, 0)))))
Ex(y, Ex(x, And(Eq(y**3, 0), Eq(x**2, 0))))
>>> s(Ex(x, Ex(y, Lt(x * x, 2 * y ** 2))))
Ex(x, Ex(y, Lt(x**2 - 2*y**2, 0)))
>>> s(Equivalent(Eq(1 + 1, 1), Eq(1, 2)))
T
>>> s(And(Eq(2 * y ** 2, 1), Eq(2 * x ** 2, 1)))
And(Eq(2*x**2 - 1, 0), Eq(2*y**2 - 1, 0))
>>> s(And(Eq(2 * x ** 2, 1), Eq(3 * x ** 2, 1)))
And(Eq(3*x**2 - 1, 0), Eq(2*x**2 - 1, 0))
>>> s(Eq(2 * x ** 2, 4 * y ** 2 + 3))
Eq(2*x**2 - 4*y**2 - 3, 0)
>>> s(Ex(y, Ex(x, Eq(x ** 2, 2 * x ** 2))))
Ex(x, Eq(x**2, 0))
>>> s(And(Lt(x, 1), Gt(x, 1)))
F
>>> s(Equivalent(Eq(x, 1), Eq(1, x)))
T
>>> s(Equivalent(Eq(x, 1), Ne(1, x)))
F
>>> s(Equivalent(Eq(4 * x + 4 * x + 2 * y ** 2, 2), Ne(x + x + x + x + y ** 2, 1)))
F
>>> s(And(Eq(x, 1), Le(x, 1)))
Eq(x - 1, 0)
>>> s(Or(Eq(x, 1), Le(x, 1)))
Le(x - 1, 0)
>>> s(And(Lt(x, 1), Le(x, 1)))
Lt(x - 1, 0)
>>> s(Or(Ge(x, 1), Le(x, 1)))
T
>>> s(Equivalent(Or(Lt(x, 1), Eq(x, 1)), Le(x, 1)))
T
>>> s(Ex(x, Equivalent(Or(Lt(x, 0), Eq(x, 0)), Le(x, 0))))
T
"""


from numbers import Real
from typing import Optional

from logic1.atomlib.sympy import BinaryAtomicFormula, Eq, Ge, Gt, Le, Lt, Ne
from logic1.firstorder.boolean import And, Or
from logic1.firstorder.truth import F, T, TruthValue
from sympy import Symbol
from sympy.logic.boolalg import Boolean
from sympy.polys import Poly
from sympy.polys.monomials import itermonomials
from sympy.polys.orderings import monomial_key
from ..abc.simp import Simplifier as BaseSimplifier

from ..util import cmp, encode


Atom = Lt | Le | Gt | Ge | Eq | Ne
Variable = Symbol

Preference = Optional[type(Lt) | type(Gt)]


def poly(φ: BinaryAtomicFormula) -> Poly:
    result = φ.args[0].as_poly()
    if not result:
        raise NotImplementedError()
    return result


class Simplifier(BaseSimplifier[Atom, Variable]):
    def __init__(self, prefer: Preference = None) -> None:
        super().__init__()
        self.prefer = prefer

    def merge(
        self,
        op: type[And | Or], φ: Atom, ψ: Atom
    ) -> Optional[BaseSimplifier.Merge | TruthValue | Atom]:
        """
        >>> from sympy.abc import x, y
        >>> s = Simplifier()
        >>> s.merge(And, Lt(x, 0), Lt(y, 0)) is None
        True
        >>> s.merge(And, Ge(x, 0), Ne(x, 0))
        Gt(x, 0)
        >>> s.merge(And, Lt(x, 0), Le(x, 0))
        L
        >>> s.merge(Or, Lt(x, 0), Le(x, 0))
        R
        >>> s.merge(And, Eq(y**3, 0), Eq(x**2, 0)) is None
        True
        >>> s.merge(Or, Gt(x, 1), Lt(x, 1))
        Ne(x, 1)
        >>> s.merge(And, Gt(x, 1), Lt(x, 1))
        F
        >>> s.merge(Or, Ge(x, 1), Le(x, 1))
        T
        >>> s.merge(Or, Lt(x, 1), Eq(x, 1))
        Le(x, 1)
        """
        fs = (φ.func, ψ.func)

        if φ == ψ:
            return BaseSimplifier.Merge.L
        elif φ.args != ψ.args:
            return None
        elif φ.func == ψ.complement_func:
            return encode(op == Or)
        elif op is And and len({Gt, Lt, Eq}.intersection({φ.func, ψ.func})) == 2:
            return F
        elif op is Or:
            if fs == (Gt, Eq):
                return Ge(*φ.args)
            elif fs == (Lt, Eq):
                return Le(*φ.args)
            elif fs == (Eq, Gt):
                return Ge(*φ.args)
            elif fs == (Eq, Lt):
                return Le(*φ.args)

        if fs == (Gt, Ge) or fs == (Lt, Le) or fs == (Eq, Ge) or fs == (Eq, Le):
            return BaseSimplifier.Merge.L if op is And else BaseSimplifier.Merge.R
        elif fs == (Ge, Gt) or fs == (Le, Lt) or fs == (Ge, Eq) or fs == (Le, Eq):
            return BaseSimplifier.Merge.R if op is And else BaseSimplifier.Merge.L
        elif fs == (Ge, Ne):
            return Gt(*φ.args) if op is And else BaseSimplifier.Merge.L
        elif fs == (Ne, Ge):
            return Gt(*φ.args) if op is And else BaseSimplifier.Merge.R
        elif fs == (Le, Ne):
            return Lt(*φ.args) if op is And else BaseSimplifier.Merge.L
        elif fs == (Ne, Le):
            return Lt(*φ.args) if op is And else BaseSimplifier.Merge.R
        elif fs == (Ge, Le) or fs == (Le, Ge):
            return Eq(*φ.args) if op is And else T
        elif fs == (Gt, Lt) or fs == (Lt, Gt):
            return F if op is And else Ne(*φ.args)
        else:
            return None

    def atom(
        self,
        φ: Atom
    ) -> Atom | TruthValue:
        # print("simplify atom got " + str(φ) + " of type " + str(type(φ)) + " and a prefer of " + str(prefer))
        lhs = φ.args[0] - φ.args[1]

        if lhs.is_zero:
            lhs = 0

        if isinstance(lhs, Real):
            # print("about to evaluate something!")
            result = φ.sympy_func(lhs, 0)
            if isinstance(result, Boolean):
                return encode(result)
            else:
                raise NotImplementedError("expected comparison relation to evaluate")

        lhs = lhs.as_poly()  # type: ignore
        lhs = (lhs / lhs.content()).as_poly()

        if (isinstance(φ, Gt | Ge) and self.prefer is Lt) or (
            isinstance(φ, Lt | Le) and self.prefer is Gt
        ):
            return φ.converse_func((-lhs).as_expr(), 0)
        elif not self.prefer or isinstance(φ, Eq | Ne):
            symbols = sorted(lhs.free_symbols, key=lambda x: x.sort_key())
            max_mon = next(
                filter(
                    lhs.coeff_monomial,
                    sorted(
                        itermonomials(symbols, lhs.degree()),
                        key=monomial_key("lex", symbols),
                        reverse=True,
                    ),
                )
            )

            if lhs.coeff_monomial(max_mon) < 0:
                return φ.converse_func((-lhs).as_expr(), 0)

        return φ.func(lhs.as_expr(), 0)

    def cmp(self, s: Atom, t: Atom) -> int:
        (sp, tp) = (poly(s), poly(t))

        if sp is None or tp is None:
            if sp is None and tp is not None:
                return -1
            elif sp is not None and tp is None:
                return 1
            else:
                raise NotImplementedError()

        if sp.degree() != tp.degree():
            return tp.degree() - sp.degree()

        symbols = sorted(sp.free_symbols.union(tp.free_symbols), key=lambda x: x.sort_key())
        mons = sorted(
            itermonomials(symbols, sp.degree()),
            key=monomial_key("igrevlex", symbols),
        )

        def coeff_monomial(p: Poly, m):
            """
            Utility function, since calling Poly.coeff_monomial with
            a monomial that does not occur in the polynomial will
            not just return None, but raise a ValueError.
            """
            try:
                result = p.coeff_monomial(m)
                return 0 if result is None else result
            except ValueError:
                return 0

        def coeffs(p: Poly):
            return tuple([coeff_monomial(p, mon) for mon in mons])

        return -cmp(coeffs(sp), coeffs(tp))


simplify = Simplifier()
