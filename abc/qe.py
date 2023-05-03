import logging
from abc import ABC, abstractmethod
from time import time
from typing import Callable, Generic, Optional, TypeVar

from logic1.firstorder import AtomicFormula, BooleanFormula
from logic1.firstorder.boolean import And, Not, Or
from logic1.firstorder.formula import Formula
from logic1.firstorder.quantified import All, QuantifiedFormula
from logic1.firstorder.truth import F, T

from ..util import matrix

α = TypeVar("α")

Matrix = BooleanFormula | AtomicFormula

logger = logging.getLogger("qe")
logger.propagate = False
streamHandler = logging.StreamHandler()
streamHandler.setFormatter(
    logging.Formatter("%(levelname)s[%(relativeCreated)0.0f ms]: %(message)s")
)
logger.addHandler(streamHandler)


class QuantifierElimination(ABC, Generic[α]):
    def __init__(
        self,
        simplify: Callable[[Formula], Formula],
        blocks=None,
        matrix=None,
        negated=None,
        pool=None,
        finished=None,
    ) -> None:
        #  __init__ is typically called without arguments so that everything is
        #  initialized with None.

        # A quantifier block is a pair (quantifier Symbol, list of variables).
        # self.blocks holds a list of quantifier Blocks.
        self.blocks: Optional[list[tuple[type[QuantifiedFormula], list[α]]]] = blocks

        # self.matrix holds a quantifier-free formula.
        self.matrix: Optional[Matrix] = matrix

        # self.blocks and self.matrix will be initialized with the PNF of the
        # input formula later on. Then elimination proceeds block-wise.

        # self.negated is bool. It is T when the list of primitive formulas
        # processed in self.pool below, originates from an All-block.
        self.negated: Optional[bool] = negated

        # self.pool is a Pool (subclass of list, s.a.) of pairs (list of
        # variables, conjunction of literals). Each pair represents a primitive
        # formula, which establishes a subproblem that we call "job".
        self.pool: Optional[list[tuple[list[α], Matrix]]] = pool

        # finished is a list of quantifier free formulas. Those are subproblems
        # from self.pool where all variables have been eliminated.
        self.finished: Optional[list[Formula]] = finished

        self.simplify: Callable[[Formula], Formula] = simplify

    def push_to_pool(self, vars_: list[α], f: Matrix) -> Optional[tuple[()]]:
        if self.pool is None:
            self.pool = []

        dnf = f.to_dnf()

        if isinstance(dnf, And | AtomicFormula):
            self.pool.append((vars_, dnf))
        elif dnf is F:
            return
        elif dnf is T:
            return ()
        elif isinstance(dnf, Or):
            self.pool.extend([(vars_.copy(), f) for f in dnf.args])  # type: ignore
        else:
            raise NotImplementedError(
                "dnf is strange: " + str(dnf) + " " + str(type(dnf))
            )

    def true(self):
        self.pool = None
        self.finished = [T]

    def qe(self, f: Formula) -> Formula:
        f = self.simplify(f)
        logging._startTime = time()  # type: ignore
        self.setup(f)
        while self.blocks:
            if self.pop_block() == ():
                self.true()
            elif self.process_pool() == ():
                self.true()
            self.collect_finished()

        assert self.matrix is not None
        return self.simplify(self.matrix.to_nnf())

    def setup(self, f: Formula) -> None:
        f = f.to_pnf()

        if not self.blocks:
            self.blocks = []
            q: Optional[type[QuantifiedFormula]] = None
            xs: list[α] = []
            fp = f
            while isinstance(fp, QuantifiedFormula):
                if q == fp.func:
                    xs.append(fp.var)
                else:
                    if q:
                        self.blocks.append((q, xs))
                    (q, xs) = (fp.func, [fp.var])
                fp = fp.arg
            if q:
                self.blocks.append((q, xs))

        if not self.matrix:
            self.matrix = matrix(f)

        logger.info(f"{self.setup.__qualname__}: {self}")

    def pop_block(self) -> Optional[tuple[()]]:
        assert self.blocks is not None
        assert self.matrix is not None

        assert self.negated is None
        assert self.pool is None
        assert self.finished is None

        (q, x) = self.blocks.pop()
        self.negated = q is All

        if self.negated:
            self.matrix = Not(self.matrix)

        if self.push_to_pool(x, self.matrix) == ():
            return ()

        self.matrix = None
        self.finished = []
        logger.info(f"{self.pop_block.__qualname__}: {self}")

    def process_pool(self) -> None:
        assert self.finished is not None
        while self.pool:
            (variables, f) = self.pool.pop()
            assert variables
            f = self.qe1p(variables.pop(), f)
            if not variables:
                self.finished.append(f)
            else:
                self.push_to_pool(variables, f)

            logger.info(f"{self.process_pool.__qualname__}: {self}")

    @abstractmethod
    def qe1p(self, v: α, f: Matrix) -> Matrix:
        # This is implemented in a subclass of this class within  a "theories"
        # module.
        ...

    def collect_finished(self) -> None:
        assert self.finished is not None

        disj = Or(*self.finished)

        if self.negated:
            disj = Not(disj)

        self.matrix = disj
        self.pool = None
        self.finished = None
        self.negated = None
        logger.info(f"{self.collect_finished.__qualname__}: {self}")

    def __repr__(self):
        # As usual, this prints the current state in format so that it can be
        # used as input. It is not really need at present, and direct use of
        # input is not possible, because the class is abstract. It is still
        # good to have it as a rawer alternative to __str__ below.
        return (
            f"QuantifierElimination(blocks={self.blocks!r}, "
            f"matrix={self.matrix!r}, "
            f"negated={self.negated!r}, "
            f"pool={self.pool!r}, "
            f"finished={self.finished!r})"
        )

    def __str__(self):
        if self.blocks is not None:
            _h = [q.__qualname__ + " " + str(v) for q, v in self.blocks]
            _h = "  ".join(_h)
            blocks = f"[{_h}]"
        else:
            blocks = None
        if self.negated is True:
            read_as = "  # read as Not All"
        elif self.negated is False:
            read_as = "  # read as Ex"
        else:
            assert self.negated is None
            read_as = ""
        if self.pool is not None:
            _h = [f"({str(job[0])}, {str(job[1])})" for job in self.pool]
            _h = ",\n                ".join(_h)
            pool = f"[{_h}]"
        else:
            pool = None
        if self.finished is not None:
            _h = [f"{str(f)}" for f in self.finished]
            _h = ",\n                ".join(_h)
            finished = f"[{_h}]"
        else:
            finished = None
        return (
            f"{self.__class__} [\n"
            f"    blocks   = {blocks},\n"
            f"    matrix   = {self.matrix},\n"
            f"    negated  = {self.negated},{read_as}\n"
            f"    pool     = {str(pool)},\n"
            f"    finished = {finished}\n"
            f"]"
        )
