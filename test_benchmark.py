import unittest

from .simplify import simplify
from .test_fixture import benchmark
from .util import size


@unittest.skip("too expensive")
class BenchmarkTest(unittest.TestCase):
    def test_benchmark(self):
        before = 710
        self.assertEqual(before, size(benchmark))
        after = size(simplify(benchmark))
        self.assertLessEqual(after, before)
        self.assertLessEqual(674, after)
