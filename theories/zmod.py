"""
>>> from logic1 import *
>>> from util import eq0, show_progress
>>> from sympy.abc import a, b, c, x, y, z
>>> show_progress(True)
>>> qe(2)(All(x, All(y, Ex(z, Eq(x + y, z)))))
T
>>> φ = Ex(x, Eq(a*x, 1))
>>> qe(6)(φ)
Or(Eq(5*a + 5, 0), Eq(4*a + 5, 0), Eq(3*a + 5, 0), Eq(2*a + 5, 0), Eq(a + 5, 0))
>>> θ = All(a, Ne(a, 0) >> φ)
>>> qe(3)(θ)
T
>>> qe(4)(θ)
F
>>> qe(2)(All(x, All(y, Equivalent(Eq(x * y, 1), Eq(x, 1) & Eq(y, 1)))))
T
>>> qe(2)(All(x, All(y, Equivalent(Eq(x + y, 1), ~ Equivalent(Eq(x, 1), Eq(y, 1))))))
T
"""

from logic1.atomlib.sympy import Eq, Ne
from logic1.firstorder.truth import TruthValue
from logic1.firstorder.quantified import QuantifiedFormula
from logic1.firstorder.boolean import Or, And, AndOr, Implies, Equivalent
from logic1.firstorder import AtomicFormula
from logic1.firstorder.formula import Formula, Ex
from sympy import Integer, Symbol

from ..abc.qe import QuantifierElimination as QuantifierEliminationBase
from .rings import Atom, Simplifier as SimplifierBase
from ..util import encode


class Simplifier(SimplifierBase):
    def __init__(self, modulus: int) -> None:
        super().__init__()
        self.modulus = modulus

    def atom(self, f: Atom) -> Atom | TruthValue:
        lhs = (f.lhs - f.rhs).expand(modulus=self.modulus)

        if lhs == Integer(0):
            return encode(isinstance(f, Eq))
        if not lhs.free_symbols:
            return encode(isinstance(f, Ne))
        else:
            return f.func(lhs, 0)


class QuantifierElimination(QuantifierEliminationBase[Symbol]):
    def __init__(self, modulus: int):
        super().__init__(Simplifier(modulus=modulus))
        self.modulus = modulus

    def set_modulus(self, modulus: int):
        self.simplify = Simplifier(modulus=modulus)
        self.modulus = modulus

    def qe1p(self, x: Symbol, f: Formula) -> Formula:
        return self.simplify(Or(*self.subs(x, f)))

    def subs(self, x: Symbol, f: Formula) -> tuple[Formula]:
        return tuple(f.subs({x: i}) for i in range(self.modulus))

    def ground(self, f: Formula) -> Formula:
        match f:
            case TruthValue() | AtomicFormula():
                return f
            case AndOr(args=args, func=func):
                return func(*map(self.ground, args))
            case Implies(args=args):
                return Implies(*map(self.ground, args))
            case Equivalent(args=args):
                return Equivalent(*map(self.ground, args))
            case QuantifiedFormula(var=x, arg=arg):
                return self.ground((Or if isinstance(f, Ex) else And)(*self.subs(x, arg)))
            case _:
                raise NotImplementedError()

    def qe(self, f: Formula, alternative: bool = False):
        return self.simplify(self.ground(f)) if alternative else super().qe(f)

    def __call__(self, f, alternative: bool = False):
        return self.qe(f, alternative=alternative)


qe = QuantifierElimination
