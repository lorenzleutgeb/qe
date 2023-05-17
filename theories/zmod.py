"""
>>> from logic1 import *
>>> from util import eq0
>>> from sympy.abc import a, b, c, x, y, z
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

from functools import partial
from typing import Optional

from logic1.atomlib.sympy import Eq, Ne
from logic1.firstorder.boolean import Or
from logic1.firstorder.formula import Formula
from sympy import Integer, Symbol

from ..abc.qe import QuantifierElimination as Base
from ..simplify import make_simplify as base_make_simplify
from ..util import encode
from .rings import term_cmp as cmp


def simplify_atom(f, modulus: Optional[int] = None):
    lhs = (f.args[0] - f.args[1]).expand(modulus=modulus)

    if lhs == Integer(0):
        return encode(isinstance(f, Eq))
    if not lhs.free_symbols:
        return encode(isinstance(f, Ne))
    else:
        return f.func(lhs, 0)


def make_simplify(modulus: int):
    return base_make_simplify(atom=partial(simplify_atom, modulus=modulus), cmp=cmp)


class QuantifierElimination(Base[Symbol]):
    """Quantifier elimination"""

    def __init__(self, modulus: int):
        super().__init__(make_simplify(modulus))
        self.modulus = modulus

    def set_modulus(self, modulus: int):
        self.simplify = make_simplify(modulus)
        self.modulus = modulus

    def qe1p(self, v: Symbol, f: Formula) -> Formula:
        return self.simplify(Or(*(f.subs({v: i}) for i in range(self.modulus))))


qe = QuantifierElimination
