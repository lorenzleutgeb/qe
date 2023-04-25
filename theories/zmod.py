import logging

import sympy

from logic1 import abc
from logic1 import atomlib
# from logic1.atomlib.sympy import Eq, Ne
from logic1.firstorder.boolean import Or, T, F
from logic1.firstorder.formula import Formula
from logic1.support.decorators import classproperty


logging.basicConfig(
    format='%(levelname)s[%(relativeCreated)0.0f ms]: %(message)s',
    level=logging.CRITICAL)


def show_progress(flag: bool = True) -> None:
    if flag:
        logging.getLogger().setLevel(logging.INFO)
    else:
        logging.getLogger().setLevel(logging.CRITICAL)


Term = sympy.Symbol
Variable = sympy.Symbol


_modulus = None


def setmod(m: int) -> int:
    global _modulus
    _tmp = _modulus
    _modulus = m
    return _tmp


class Eq(atomlib.sympy.Eq):

    @classproperty
    def complement_func(cls):
        """The complement relation Ne of Eq.
        """
        return Ne

    @classproperty
    def converse_func(cls):
        """The converse relation Eq of Eq.
        """
        return Eq

    def simplify(self):
        lhs = self.args[0] - self.args[1]
        lhs = lhs.expand(modulus=_modulus)
        if lhs == sympy.Integer(0):
            return T
        if not lhs.free_symbols:
            return F
        return Eq(lhs, 0)


class Ne(atomlib.sympy.Ne):

    @classproperty
    def complement_func(cls):
        """The complement relation Eq of Ne.
        """
        return Eq

    @classproperty
    def converse_func(cls):
        """The converse relation Ne of Ne.
        """
        return Ne

    def simplify(self):
        lhs = self.args[0] - self.args[1]
        lhs = lhs.expand(modulus=_modulus)
        if lhs == sympy.Integer(0):
            return F
        if not lhs.free_symbols:
            return T
        return Ne(lhs, 0)


class QuantifierElimination(abc.qe.QuantifierElimination):
    """Quantifier elimination
    """

    # Instance methods
    def __call__(self, f, modulus: int = None):
        if modulus is not None:
            save_modulus = setmod(modulus)
            result = self.qe(f)
            setmod(save_modulus)
            return result
        return self.qe(f)

    def qe1p(self, v: Variable, f: Formula) -> Formula:
        return Or(*(f.subs({v: i}) for i in range(_modulus)))

    @staticmethod
    def is_valid_atom(f: Formula) -> bool:
        return isinstance(f, (Eq, Ne))


qe = quantifier_elimination = QuantifierElimination()
