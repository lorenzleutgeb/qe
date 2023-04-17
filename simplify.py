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

from sympy import Expr as Term, Symbol as Variable, Add, Mul, true, false
from sympy.abc import x, y
from sympy.logic.boolalg import Boolean, BooleanTrue, BooleanFalse
from sympy.polys import Poly
from sympy.polys.domains import RR
from sympy.polys.monomials import itermonomials
from sympy.polys.orderings import lex, monomial_key
from sympy.polys.rings import ring, PolyElement

# >>> R, x, y, z = ring("x,y,z", RR, lex)
# >>> type(x)
# <class 'sympy.polys.rings.PolyElement'>


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


def simplify(φ: Formula) -> Formula:
    """
    >>> simplify(T)
    T
    >>> simplify(F)
    F
    >>> simplify(Ex(x, And(T, Not(F))))
    T
    >>> simplify(All(x, Or(F, F)))
    F
    >>> simplify(Or(T, F))
    T
    >>> simplify(And(T, F))
    F
    >>> simplify(Implies(T, T))
    T
    >>> simplify(Implies(T, F))
    F
    >>> simplify(Implies(F, F))
    T
    >>> simplify(Equivalent(F, F))
    T
    >>> simplify(Equivalent(T, F))
    F
    >>> simplify(Equivalent(F, F))
    T
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
    >>> simplify(Equivalent(Eq(x, 1), Eq(1, x)))
    And(Or(Ne(x - 1, 0), Eq(1 - x, 0)), Or(Eq(x - 1, 0), Ne(1 - x, 0)))
    >>> simplify(Eq(Mul(2, Mul(x, x)), Add(Mul(4, Mul(y, y)), 3)))
    Eq(2*x**2 - 4*y**2 - 3, 0)
    >>> simplify(Ex(y, Ex(x, Eq(Mul(x, x), Mul(2, Mul(x, x))))))
    Ex(x, Eq(-x**2, 0))
    """

    def simplify_atom(φ: AtomicFormula) -> Formula:
        (l, r) = φ.args

        if isinstance(l, Real) and isinstance(r, Real):
            result = φ.sympy_func(l, r)
            if isinstance(result, Boolean):
                return encode(result)
            else:
                raise NotImplementedError("expected comparison relation to evaluate")

        l = (l - r).as_poly()

        if l is None:
            raise NotImplementedError("expected to get a polynomial")

        (ρ, λ) = (
            (φ.converse_func, -1)
            if isinstance(φ, Gt) or isinstance(φ, Ge)
            else (φ.func, 1)
        )
        return ρ(l / l.content() * λ, 0)  # type: ignore

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
        result = simplify_atom(φ)
        return result

    # φ = φ' → φ''
    elif isinstance(φ, Implies):
        return simplify(And(implies(*φ.args)))

    # φ = φ' ↔ φ''
    elif isinstance(φ, Equivalent):
        return simplify(And(implies(*φ.args), implies(*reversed(φ.args))))

    # φ = ○x.ψ where ○ is ∀ or ∃
    elif isinstance(φ, QuantifiedFormula):
        (x, ψ) = (φ.var, φ.arg)
        return simplify(ψ) if x not in ψ.get_vars().free else φ.func(x, simplify(ψ))

    # φ = ¬ψ
    elif isinstance(φ, Not):
        ψ = φ.arg
        if isinstance(ψ, TruthValue):
            return encode(ψ is F)
        elif isinstance(ψ, AndOr):
            # De Morgan's Law
            return φ.dual_func(*[simplify(inv_not(x)) for x in φ.args])
        elif isinstance(ψ, BinaryAtomicFormula):
            # Push negation down into atomic formula.
            return simplify(ψ.dual_func(*ψ.args))
        else:
            raise NotImplemented("unreachable")

    # φ = ψ₁ ○ … ○ ψₙ where ○ is ∧ or ∨
    elif isinstance(φ, AndOr):
        (id, dual) = (T, F) if isinstance(φ, And) else (F, T)
        args = tuple(filter(lambda x: x is not id, map(simplify, φ.args)))
        if not args:
            return id
        elif dual in args:
            return dual
        else:
            return φ.func(*sorted(args, key=cmp_to_key(formula_cmp)))  # type: ignore

    return φ
