from functools import partial
from typing import Optional

import sympy
from logic1.atomlib.sympy import Eq, Ne
from logic1.firstorder.boolean import Or
from logic1.firstorder.formula import Formula

from ..abc.qe import QuantifierElimination as Base
from ..simplify import make_simplify
from ..util import encode

Term = sympy.Expr
Variable = sympy.Symbol


def simplify_atom(f, modulus: Optional[int] = None):
    lhs = (f.args[0] - f.args[1]).expand(modulus=modulus)

    if lhs == sympy.Integer(0):
        return encode(isinstance(f, Eq))
    if not lhs.free_symbols:
        return encode(isinstance(f, Ne))
    else:
        return f.func(lhs, 0)


def make_simplify_atom(modulus: Optional[int] = None):
    return partial(simplify_atom, modulus=modulus)


class QuantifierElimination(Base):
    """Quantifier elimination"""

    def __init__(self, modulus: Optional[int] = None):
        super().__init__(make_simplify(atom=make_simplify_atom(modulus=modulus)))
        self.modulus = modulus

    def __call__(self, f):
        return self.qe(f)

    def qe1p(self, v: Variable, f: Formula) -> Formula:
        assert self.modulus is not None
        return self.simplify(Or(*(f.subs({v: i}) for i in range(self.modulus))))


qe = quantifier_elimination = QuantifierElimination
