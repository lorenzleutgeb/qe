from abc import ABC, abstractmethod
import logging
from time import time

from logic1.firstorder.boolean import And, Or, Not
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import QuantifiedFormula, All
from logic1.firstorder.truth import T, F


Variable = Any


class FoundT(Exception):
    # Signals that we have found T as an elimination result of 1-primitive
    # formula. At that point we know that the overall QE result is T or F,
    # and we can stop.
    pass


class QuantifierElimination(ABC):

    class Pool(list):
        def __init__(self, vars_: list[Variable], f: Formula) -> None:
            self.push(vars_, f)

        def push(self, vars_: list[Variable], f: Formula) -> None:
            # Compute a DNF of formula. Combine each conjunction in the DNF
            # with vars_ and push it into the pool. Take care of T (exception)
            # and F (ignore)
            ...

    def __init__(self, blocks=None, matrix=None, negated=None, pool=None,
                 finished=None) -> None:

        # A quantifier block is a pair (quantifier Symbol, list of variables).
        # blocks holds a list of quantifier Blocks.
        self.blocks = blocks

        # matrix holds a quantifier-free formula.
        self.matrix = matrix

        # blocks and matrix will be initialized with the PNF of the input
        # formula. Then elimination proceeds block-wise.

        # negated is bool. It is T if the Ex-block currently processed below
        # originally was an All-block
        self.negated = negated

        # pool is a Pool (subclass of list, s.a.) of pairs (list of variables,
        # conjunction of literals). Each pair establishes a subproblem, where
        # the variables are considered existentially quantified.
        self.pool = pool

        # finished is a list of quantifier free formulas. Those are formulas
        # from the pool where all variables have been eliminated.
        self.finished = finished

    def qe(self, f: Formula) -> Formula:
        logging._startTime = time()
        self.setup(f)
        while self.blocks:
            try:
                self.pop_block()
                self.process_pool()
            except FoundT:
                self.pool = None
                self.finished = [T]
            self.collect_finished()
        return self.matrix.to_nnf().simplify()

    def setup(self, f: Formula) -> None:
        # Compute a PNF of f, and populate self.blocks and self.matrix.
        ...
        logging.info(f'{self.setup.__qualname__}: {self}')

    def pop_block(self) -> None:
        # Remove the innermost block from self.blocks.
        # Set negated to T or F depending on the quantifier symbol of innermost block.
        # Push(innermost block, self.matrix) into the pool.
        # Set self.matrix to None
        ...

    def process_pool(self) -> None:
        while self.pool:
            # Pop a pair (variables, f)
            # Select a variable v from variables
            # Apply self.qe1p(v, f)
            # If v was the last variable, then push the result to self.finished
            # Else push back to the pool with the remaining variables
            ...
            logging.info(f'{self.process_pool.__qualname__}: {self}')

    @abstractmethod
    def qe1p(self, v: Variable, f: Formula) -> Formula:
        # This is implemented elsewhere in a subclass of this class. Those
        # '...' are should remain.
        ...

    def collect_finished(self) -> None:
        # Convert the list self.finished to a disjunction D
        # Negate D if self.negated is T
        # Set self.matrix to D
        # self.pool, self.finished, and self.negated become None
        ...
        logging.info(f'{self.collect_finished.__qualname__}: {self}')

    def __repr__(self):
        return (f'QuantifierElimination(blocks={self.blocks!r}, '
                f'matrix={self.matrix!r}, '
                f'negated={self.negated!r}, '
                f'pool={self.pool!r}, '
                f'finished={self.finished!r})')

    def __str__(self):
        if self.blocks is not None:
            _h = [q.__qualname__ + ' ' + str(v) for q, v in self.blocks]
            _h = '  '.join(_h)
            blocks = f'[{_h}]'
        else:
            blocks = None
        if self.negated is None:
            read_as = ''
        elif self.negated is False:
            read_as = '  # read as Ex'
        else:
            assert self.negated is True
            read_as = '  # read as Not All'
        if self.pool is not None:
            _h = [f'({str(job[0])}, {str(job[1])})' for job in self.pool]
            _h = ',\n                '.join(_h)
            pool = f'[{_h}]'
        else:
            pool = None
        if self.finished is not None:
            _h = [f'{str(f)}' for f in self.finished]
            _h = ',\n                '.join(_h)
            finished = f'[{_h}]'
        else:
            finished = None
        return (f'{self.__class__} [\n'
                f'    blocks   = {blocks},\n'
                f'    matrix   = {self.matrix},\n'
                f'    negated  = {self.negated},{read_as}\n'
                f'    pool     = {str(pool)},\n'
                f'    finished = {finished}\n'
                f']')
