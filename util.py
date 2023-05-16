import logging
from typing import Any, Callable, Optional, TypeGuard, TypeVar, Iterator

from logic1.atomlib.sympy import Eq
from logic1.firstorder import AtomicFormula, BooleanFormula
from logic1.firstorder.formula import And, Formula, Not, Or
from logic1.firstorder.boolean import AndOr
from logic1.firstorder.quantified import QuantifiedFormula
from logic1.firstorder.truth import F, T, TruthValue
from sympy import Expr

α = TypeVar("α")


def list_isinstance(xs: list[Any], τ: type[α]) -> TypeGuard[list[α]]:
    return all(isinstance(x, τ) for x in xs)


def tuple_isinstance(xs: tuple[Any], τ: type[α]) -> TypeGuard[tuple[α]]:
    return all(isinstance(x, τ) for x in xs)


Atom = AtomicFormula | TruthValue


def var_occs(f: Formula) -> Iterator[Any]:
    for atom in atoms(f):
        yield from atom.get_vars().free


def atoms(f: Formula) -> Iterator[Atom]:
    """
    Generates all atoms of f.
    """
    if isinstance(f, Atom):
        yield f
    elif isinstance(f, QuantifiedFormula):
        yield from atoms(f.arg)
    elif isinstance(f, AndOr):
        for arg in f.args:
            yield from atoms(arg)
    else:
        raise NotImplementedError("unexpected type of formula")


def sub(f: Formula) -> Iterator[Formula]:
    """
    Generates all subformulae of f.
    """
    yield f
    if isinstance(f, Atom):
        return
    elif isinstance(f, QuantifiedFormula):
        yield from sub(f.arg)
    elif isinstance(f, AndOr):
        for arg in f.args:
            yield from sub(arg)
    else:
        raise NotImplementedError("unexpected type of formula")


def size(φ: Formula) -> int:
    if isinstance(φ, AtomicFormula):
        return 1
    elif isinstance(φ, TruthValue):
        return 0
    else:
        return sum(map(size, φ.args))


def closure(τ: type[QuantifiedFormula], φ: Formula) -> Formula:
    for var in φ.get_vars().free:
        φ = τ(var, φ)
    return φ


def no_alternations(τ: type, φ: Formula) -> bool:
    """
    Assumes that φ is in prenex normal form.

    Returns true if all quantifiers in the prefix of φ are
    of type τ.

    >>> from logic1.firstorder.quantified import Ex, All
    >>> from sympy.abc import x, y
    >>> no_alternations(Ex, Ex(x, Ex(y, T)))
    True
    >>> no_alternations(Ex, All(x, Ex(y, T)))
    False
    >>> no_alternations(All, All(x, All(y, T)))
    True
    >>> no_alternations(Ex, All(x, All(y, T)))
    False
    """
    return not isinstance(φ, QuantifiedFormula) or (
        isinstance(φ, τ) and no_alternations(τ, φ.arg)
    )


def is_conjunctive(φ: Formula) -> bool:
    """
    Assumes that φ is in prenex normal form.

    >>> from logic1.firstorder.quantified import Ex
    >>> from sympy.abc import x
    >>> is_conjunctive(Ex(x, T))
    True
    >>> is_conjunctive(Ex(x, Or(T, T)))
    False
    >>> is_conjunctive(Ex(x, And(T, T)))
    True
    """
    if isinstance(φ, AtomicFormula | TruthValue):
        return True
    elif isinstance(φ, QuantifiedFormula):
        return is_conjunctive(matrix(φ))
    elif isinstance(φ, Not):
        return isinstance(φ.arg, AtomicFormula)
    elif isinstance(φ, And):
        return all(map(is_conjunctive, φ.args))
    else:
        return False


def matrix(φ: Formula) -> BooleanFormula | AtomicFormula:
    """
    Assumes that φ is in prenex normal form.

    Returns the matrix of the formula.
    """
    if isinstance(φ, QuantifiedFormula):
        return matrix(φ.arg)
    else:
        assert isinstance(φ, BooleanFormula | AtomicFormula)
        return φ


def conjunctive_core(φ: Formula) -> list[Formula]:
    """
    Assumes that φ is in prenex normal form, all quantifiers are existential,
    and the formula is conjunctive.
    """
    if not is_conjunctive(φ):
        raise ValueError("φ is not conjunctive")
    φ = matrix(φ)
    return list(φ.args) if isinstance(φ, And) else [φ]


def encode(x) -> TruthValue:
    """
    >>> encode(True)
    T
    >>> encode(False)
    F
    >>> encode([])
    F
    >>> encode(0)
    F
    >>> encode(1)
    T
    """
    return T if x else F


def cmp(a, b) -> int:
    if a < b:
        return -1
    elif a > b:
        return 1
    elif a == b:
        return 0
    else:
        raise ValueError(
            "ordering for " + str(type(a)) + " " + str(type(b)) + " is not total"
        )


def inv_not(φ: Formula) -> Formula:
    """
    Returns a formula equivalent to ¬φ, exploiting the fact
    that ¬ is involutive (φ ≡ ¬¬φ), i.e. the result of applying this
    function to ¬ψ will not be ¬¬ψ but rather ψ.
    """
    return φ.arg if isinstance(φ, Not) else Not(φ)


def implies(φ: Formula, ψ: Formula) -> Or:
    """
    Given φ and ψ, returns a formula equivalent to ¬φ ∨ ψ,
    which in turn is equivalent to the implication φ → ψ.
    """
    return Or(inv_not(φ), ψ)


def show_progress(flag: bool = True, logger: Optional[str] = "qe") -> None:
    if flag:
        logging.getLogger(logger).setLevel(logging.DEBUG)
    else:
        logging.getLogger(logger).setLevel(logging.WARN)


def eq0(e: Expr) -> Eq:
    return Eq(e, 0)


def conjunctive(φ) -> list[AtomicFormula]:
    if isinstance(φ, And) and tuple_isinstance(φ.args, AtomicFormula):
        return list(φ.args)
    else:
        assert isinstance(φ, AtomicFormula)
        return [φ]
