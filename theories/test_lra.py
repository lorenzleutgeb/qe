import logging
import unittest

from logic1.atomlib.sympy import Eq, Ge, Gt, Lt
from logic1.firstorder.boolean import And
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import Ex
from logic1.firstorder.truth import F, T
from sympy.abc import x, y, z

from ..util import closure, show_progress
from .lra import qe
from .rings import make_simplify

simplify_lt = make_simplify(prefer=Lt)


def exsimp(*conj: Formula) -> Formula:
    return simplify_lt(closure(Ex, And(*conj)))


class FourierMotzkinTests(unittest.TestCase):
    def test_simple1(self):
        f = exsimp(Ge(x + y - 2 * z, 2), Ge(-x - 3 * y + z, 0), Ge(y + z, 1))
        show_progress(True)
        f = qe(f)
        self.assertEqual(f, T)
        # self.assertEqual(matrix(f), And(Le(2 * y + z + 2, 0), Le(-y - z + 1, 0)))
        # self.assertEqual(And(Le(4 - z, 0)))
        # self.assertEqual(matrix(fme(f, z)), T)

    def test_simple2(self):
        f = exsimp(
            Ge(x + y + 2 * z, 1),
            Ge(-x + y + z, 2),
            Ge(x - y + z, 1),
            Ge(-y - 3 * z, 0),
        )

        self.assertEqual(qe(f), F)

    def test_simple3(self):
        f = exsimp(
            Ge(x + y + 2 * z, 1),
            Ge(-x + y + z, 2),
            Ge(x - y + z, 1),
            Ge(-y - 3 * z, 0),
        )
        self.assertEqual(qe(f), F)

    def test_simple4(self):
        logging.basicConfig(level=logging.DEBUG)
        f = exsimp(Ge(x, 1), Lt(y, 0), Gt(y, 0))
        self.assertEqual(qe(f), F)
        # self.assertEqual(f, Ex(y, And(Lt(y, 0), Lt(-y, 0))))

    def test_eq1(self):
        f = exsimp(Eq(x, 1), Eq(y, x))
        # self.assertEqual(f, Ex(y, Eq(y - 1, 0)))
        self.assertEqual(qe(f), T)

    def test_eq2(self):
        f = exsimp(Eq(x, 1), Eq(y, x), Eq(y, 2))
        # self.assertEqual(f, Ex(y, And(Eq(y - 1, 0), Eq(y - 2, 0))))
        self.assertEqual(qe(f), F)

    def test_eq3(self):
        f = exsimp(Eq(x, 3), Eq(y, 3 * x))
        # self.assertEqual(f, Ex(y, Eq(y - 9, 0)))
        self.assertEqual(qe(f), T)


if __name__ == "__main__":
    unittest.main()
