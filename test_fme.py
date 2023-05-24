import logging
import unittest

from logic1.atomlib.sympy import Eq, Ge, Gt, Le, Lt
from logic1.firstorder.boolean import And
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import Ex
from logic1.firstorder.truth import F, T
from sympy.abc import x, y, z

from .fme import fme
from .theories.rings import Simplifier
from .util import closure, matrix

simplify_lt = Simplifier(Lt)


def exsimp(*conj: Formula) -> Formula:
    return simplify_lt(closure(Ex, And(*conj).to_nnf()))


class FourierMotzkinTests(unittest.TestCase):
    def test_simple1(self):
        f = exsimp(Ge(x + y - 2 * z, 2), Ge(-x - 3 * y + z, 0), Ge(y + z, 1))
        f = fme(f, x)
        self.assertEqual(matrix(f), And(Le(2 * y + z + 2, 0), Le(-y - z + 1, 0)))

        g = fme(f, y, eliminate_unbounded=False)
        self.assertEqual(
            matrix(g),
            And(
                Le(4 - z, 0),
            ),
        )
        self.assertEqual(matrix(fme(f, z)), T)

        h = fme(f, y)
        self.assertEqual(
            matrix(h),
            And(
                T,
            ),
        )

    def test_simple2(self):
        f = exsimp(
            Ge(x + y + 2 * z, 1),
            Ge(-x + y + z, 2),
            Ge(x - y + z, 1),
            Ge(-y - 3 * z, 0),
        )

        f = fme(f, x, eliminate_unbounded=False)
        f = fme(f, y, eliminate_unbounded=False)

        self.assertEqual(fme(f, z), F)

    def test_simple3(self):
        f = exsimp(
            Ge(x + y + 2 * z, 1),
            Ge(-x + y + z, 2),
            Ge(x - y + z, 1),
            Ge(-y - 3 * z, 0),
        )

        f = fme(f, x)
        f = fme(f, y)

        self.assertEqual(fme(f, z), F)

    def test_simple4(self):
        logging.basicConfig(level=logging.DEBUG)
        f = exsimp(Ge(x, 1), Lt(y, 0), Gt(y, 0))
        f = fme(f, x)
        self.assertEqual(f, Ex(y, And(Lt(y, 0), Lt(-y, 0))))
        f = fme(f, y)
        self.assertEqual(f, F)

    def test_eq1(self):
        f = exsimp(Eq(x, 1), Eq(y, x))
        f = fme(f, x)
        self.assertEqual(f, Ex(y, Eq(y - 1, 0)))
        f = fme(f, y)
        self.assertEqual(f, T)

    def test_eq2(self):
        f = exsimp(Eq(x, 1), Eq(y, x), Eq(y, 2))
        f = fme(f, x)
        self.assertEqual(f, Ex(y, And(Eq(y - 1, 0), Eq(y - 2, 0))))
        f = fme(f, y)
        self.assertEqual(f, F)

    def test_eq3(self):
        f = exsimp(Eq(x, 3), Eq(y, 3 * x))
        f = fme(f, x)
        self.assertEqual(f, Ex(y, Eq(y - 9, 0)))
        f = fme(f, y)
        self.assertEqual(f, T)


if __name__ == "__main__":
    unittest.main()
