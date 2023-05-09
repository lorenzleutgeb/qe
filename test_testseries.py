import unittest

from .simplify import simplify
from .testseries1 import testseries1
from .testseries2 import testseries2
from .util import size


class TestTestseries(unittest.TestCase):
    def test_testseries1(self):
        before = 710
        self.assertEqual(before, size(testseries1))
        after = size(simplify(testseries1))
        self.assertLessEqual(after, before)
        self.assertLessEqual(674, after)

    def test_testseries2(self):
        before = 1420
        self.assertEqual(before, size(testseries2))
        after = size(simplify(testseries2))
        self.assertLessEqual(after, before)
        self.assertLessEqual(935, after)

