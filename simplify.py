from functools import cmp_to_key
from numbers import Real

from logic1.atomlib.sympy import (
    AtomicFormula,
    BinaryAtomicFormula,
    Eq,
    Ne,
    Term,
    Gt,
    Lt,
    Ge,
    Le,
)
from logic1.firstorder.boolean import AndOr, And, Or, Not, Implies, Equivalent
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import QuantifiedFormula, All, Ex
from logic1.firstorder.truth import T, F, TruthValue

from sympy import Add, Mul, true, false
from sympy.abc import x, y
from sympy.logic.boolalg import Boolean, BooleanTrue, BooleanFalse
from sympy.polys import Poly
from sympy.polys.monomials import itermonomials
from sympy.polys.orderings import monomial_key

from itertools import combinations


def encode(x) -> TruthValue:
    """
    >>> encode(True)
    T
    >>> encode(False)
    F
    >>> encode([])
    F
    >>> encode(0)
    F
    >>> encode(1)
    T
    >>> encode(BooleanFalse())
    F
    >>> encode(BooleanTrue())
    T
    >>> encode(false)
    F
    >>> encode(true)
    T
    """
    return T if x else F


def cmp(a, b) -> int | None:
    if a < b:
        return -1
    elif a > b:
        return 1
    elif a == b:
        return 0
    else:
        return None


def merge(
    op: type[AndOr], φ: BinaryAtomicFormula, ψ: BinaryAtomicFormula
) -> BinaryAtomicFormula | TruthValue | None:
    """
    >>> merge(And, Lt(x, 0), Lt(y, 0)) is None
    True
    >>> merge(And, Ge(x, 0), Ne(x, 0))
    Gt(x, 0)
    >>> merge(And, Lt(x, 0), Le(x, 0))
    Lt(x, 0)
    >>> merge(Or, Lt(x, 0), Le(x, 0))
    Le(x, 0)
    >>> merge(And, Eq(y**3, 0), Eq(x**2, 0)) is None
    True
    >>> merge(Or, Gt(x, 1), Lt(x, 1))
    T
    >>> merge(Or, Ge(x, 1), Le(x, 1))
    T
    """

    if φ == ψ:
        return φ
    elif φ.args != ψ.args:
        return None
    elif (
        φ.func == ψ.complement_func
        or len({Gt, Lt, Eq}.intersection({φ.func, ψ.func})) == 2
    ):
        return encode(op == Or)

    fs = (φ.func, ψ.func)

    if fs == (Gt, Ge) or fs == (Lt, Le) or fs == (Eq, Ge) or fs == (Eq, Le):
        return φ if op is And else ψ
    elif fs == (Ge, Gt) or fs == (Le, Lt) or fs == (Ge, Eq) or fs == (Le, Eq):
        return ψ if op is And else φ
    elif fs == (Ge, Ne):
        return Gt(*φ.args) if op is And else φ
    elif fs == (Ne, Ge):
        return Gt(*φ.args) if op is And else ψ
    elif fs == (Le, Ne):
        return Lt(*φ.args) if op is And else φ
    elif fs == (Ne, Le):
        return Lt(*φ.args) if op is And else ψ
    elif fs == (Ge, Le) or fs == (Le, Ge):
        return Eq(*φ.args) if op is And else T
    elif fs == (Gt, Lt) or fs == (Lt, Gt):
        return Ne(*φ.args) if op is And else None
    else:
        return None


def simplify(φ: Formula, prefer: type[Lt] | type[Gt] | None = None) -> Formula:
    """
    >>> simplify(Eq(x - 2, x - 2))
    T
    >>> simplify(Ex(x, Equivalent(Or(Lt(x, 0), Eq(x, 0)), Le(x, 0))))
    T
    >>> simplify(Equivalent(Or(Lt(x, 1), Eq(x, 1)), Le(x, 1)))
    T
    >>> simplify(And(Ge(x, 0), Ne(x, 0)))
    Gt(x, 0)
    >>> simplify(Not(Le(x - 1, 0)))
    Gt(x - 1, 0)
    >>> simplify(Implies(Lt(x, 1), Le(x, 1)))
    T
    >>> simplify(Ex(x, And(T, Not(F))))
    T
    >>> simplify(All(x, Or(F, F)))
    F
    >>> simplify(Eq(x, 1))
    Eq(x - 1, 0)
    >>> simplify(Eq(1, x))
    Eq(x - 1, 0)
    >>> simplify(Ne(-1, x))
    Ne(x + 1, 0)
    >>> simplify(Eq(-1, x))
    Eq(x + 1, 0)
    >>> simplify(Lt(x, 0))
    Lt(x, 0)
    >>> simplify(Lt(x, 0), Lt)
    Lt(x, 0)
    >>> simplify(Lt(x, 0), Gt)
    Gt(-x, 0)
    >>> simplify(Lt(-x, 0))
    Gt(x, 0)
    >>> simplify(Ex(y, Ex(x, And(Eq(Mul(x, x), 0), Eq(Mul(y, Mul(y, y)), 0)))))
    Ex(y, Ex(x, And(Eq(y**3, 0), Eq(x**2, 0))))
    >>> simplify(Ex(x, Ex(y, Lt(Mul(x, x), Mul(2, Mul(y, y))))))
    Ex(x, Ex(y, Lt(x**2 - 2*y**2, 0)))
    >>> simplify(Equivalent(Eq(Add(1, 1), 1), Eq(1, 2)))
    T
    >>> simplify(And(Eq(2 * y ** 2, 1), Eq(2 * x ** 2, 1)))
    And(Eq(2*x**2 - 1, 0), Eq(2*y**2 - 1, 0))
    >>> simplify(And(Eq(2 * x ** 2, 1), Eq(3 * x ** 2, 1)))
    And(Eq(3*x**2 - 1, 0), Eq(2*x**2 - 1, 0))
    >>> simplify(Eq(Mul(2, Mul(x, x)), Add(Mul(4, Mul(y, y)), 3)))
    Eq(2*x**2 - 4*y**2 - 3, 0)
    >>> simplify(Ex(y, Ex(x, Eq(Mul(x, x), Mul(2, Mul(x, x))))))
    Ex(x, Eq(x**2, 0))
    >>> simplify(And(Lt(x, 1), Gt(x, 1)))
    F
    >>> simplify(Equivalent(Eq(x, 1), Eq(1, x)))
    T
    >>> simplify(Equivalent(Eq(x, 1), Ne(1, x)))
    F
    >>> simplify(Equivalent(Eq(4 * x + 4 * x + 2 * y ** 2, 2), Ne(x + x + x + x + y ** 2, 1)))
    F
    >>> simplify(And(Eq(x, 1), Le(x, 1)))
    Eq(x - 1, 0)
    >>> simplify(Or(Eq(x, 1), Le(x, 1)))
    Le(x - 1, 0)
    >>> simplify(And(Lt(x, 1), Le(x, 1)))
    Lt(x - 1, 0)
    >>> simplify(Or(Ge(x, 1), Le(x, 1)))
    T
    """

    def rec(φ: Formula) -> Formula:
        return simplify(φ, prefer)

    def term_cmp(s: Term, t: Term):
        if isinstance(s, Real) and isinstance(t, Real):
            return t - s

        (sp, tp) = (s.as_poly(), t.as_poly())

        if sp is None or tp is None:
            if sp is None and tp is not None:
                return -1
            elif sp is not None and tp is None:
                return 1
            else:
                raise NotImplementedError()

        if sp.degree() != tp.degree():
            return tp.degree() - sp.degree()

        symbols = sorted(
            sp.free_symbols.union(tp.free_symbols), key=lambda x: x.sort_key()
        )
        mons = sorted(
            itermonomials(symbols, sp.degree()),
            key=monomial_key("lex", symbols),
            reverse=True,
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

        return -cmp(coeffs(sp), coeffs(tp))  # type: ignore

    def formula_cmp(φ: Formula, ψ: Formula):
        if isinstance(φ, AtomicFormula) and isinstance(ψ, AtomicFormula):
            # Assumes that both atomic formulae are simplified.
            return term_cmp(φ.args[0], ψ.args[0])
        elif isinstance(φ, AtomicFormula) and not isinstance(ψ, AtomicFormula):
            return -1
        elif not isinstance(φ, AtomicFormula) and isinstance(ψ, AtomicFormula):
            return 1
        else:
            return 0

    def inv_not(φ: Formula) -> Formula:
        """
        Returns a formula equivalent to ¬φ, exploiting the fact
        that ¬ is involutive (φ ≡ ¬¬φ), i.e. the result of applying this
        function to ¬ψ will not be ¬¬ψ but rather ψ.
        """
        return φ.arg if isinstance(φ, Not) else Not(φ)

    def implies(φ: Formula, ψ: Formula) -> Or:
        """
        Given φ and ψ, returns a formula equivalent to ¬φ ∨ ψ,
        which in turn is equivalent to the implication φ → ψ.
        """
        return Or(inv_not(φ), ψ)

    # φ = ○ where ○ is ⊤ or ⊥
    if isinstance(φ, TruthValue):
        return φ

    # φ = s ○ t where ○ is one of >, ≥, <, ≤, =, ≠
    elif isinstance(φ, BinaryAtomicFormula):
        lhs = φ.args[0] - φ.args[1]

        if lhs.is_zero:
            lhs = 0

        if isinstance(lhs, Real):
            result = φ.sympy_func(lhs, 0)
            if isinstance(result, Boolean):
                return encode(result)
            else:
                raise NotImplementedError("expected comparison relation to evaluate")

        lhs = lhs.as_poly()  # type: ignore
        lhs = (lhs / lhs.content()).as_poly()

        # This type guard is necessary since there is no BinaryAtomicFormula.converse_func
        if not (
            isinstance(φ, Lt)
            or isinstance(φ, Le)
            or isinstance(φ, Gt)
            or isinstance(φ, Ge)
            or isinstance(φ, Eq)
            or isinstance(φ, Ne)
        ):
            raise ValueError("unexpected binary atomic formula")

        if ((isinstance(φ, Gt) or isinstance(φ, Ge)) and prefer is Lt) or (
            (isinstance(φ, Lt) or isinstance(φ, Le)) and prefer is Gt
        ):
            return φ.converse_func((-lhs).as_expr(), 0)
        elif not prefer or (isinstance(φ, Eq) or isinstance(φ, Ne)):
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

        return φ.func(lhs.as_expr(), 0)  # type: ignore

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
        ψ = φ.arg
        if isinstance(ψ, TruthValue):
            return encode(ψ is F)
        elif isinstance(ψ, AndOr):
            # De Morgan's Law
            return rec(ψ.dual_func(*[inv_not(x) for x in ψ.args]))
        elif isinstance(ψ, BinaryAtomicFormula):
            # Push negation down into atomic formula.
            return rec(ψ.complement_func(*ψ.args))
        else:
            raise NotImplementedError("unreachable")

    # φ = ψ₁ ○ … ○ ψₙ where ○ is ∧ or ∨
    elif isinstance(φ, AndOr):
        (id, dual) = (T, F) if isinstance(φ, And) else (F, T)
        args = set(filter(lambda x: x is not id, map(rec, φ.args)))
        if not args:
            return id
        if len(args) == 1:
            return next(iter(args))
        elif dual in args:
            return dual
        elif all([isinstance(x, BinaryAtomicFormula) for x in args]):  # type: ignore
            # TODO: Replace this mess with something beautiful.
            changed = True
            while changed:
                changed = False
                for (a, b) in combinations(args, 2):
                    m = merge(φ.func, a, b)  # type: ignore
                    if m is None:
                        continue
                    if m == a:
                        args.remove(b)
                        changed = True
                    elif m == b:
                        args.remove(a)
                        changed = True
                    elif m == id:
                        args.remove(a)
                        args.remove(b)
                        changed = True
                    elif m == dual:
                        return dual
                    elif m != a and m != b:
                        args.remove(a)
                        args.remove(b)
                        args.add(m)
                        changed = True
        return φ.func(*sorted(args, key=cmp_to_key(formula_cmp)))  # type: ignore

    return φ
