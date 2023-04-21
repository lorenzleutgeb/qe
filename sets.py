"""
>>> from sympy.abc import x, y, z
>>> from logic1.firstorder.quantified import Ex, All
>>> simplify(And(Ne(x, y), Ne(y, z)))
And(Ne(x, y), Ne(y, z))
>>> simplify(And(Ne(x, x), Ne(y, z)))
F
>>> simplify(And(Eq(x, x), Eq(y, y)))
T
>>> simplify(And(Ne(x, y), Ne(y, z), Ne(z, y)))
And(Ne(x, y), Ne(y, z))
"""

from logic1.firstorder.formula import And, Or
from logic1.firstorder.truth import TruthValue
from logic1.atomlib.sympy import Eq, Ne, AtomicFormula
from typing import Optional
from simplify import Merge, encode, make_simplify
from sympy import Symbol


def merge(
    ctx: type[And | Or], φ: AtomicFormula, ψ: AtomicFormula
) -> Optional[Merge | TruthValue]:
    assert isinstance(φ, Eq | Ne) and isinstance(φ, Eq | Ne)

    if φ.args == ψ.args and {φ.func, ψ.func} == {Eq, Ne}:
        return encode(ctx is Or)

    return None


def simplify_atom(φ: Eq | Ne) -> Eq | Ne | TruthValue:
    (lhs, rhs) = φ.args
    assert isinstance(lhs, Symbol) and isinstance(rhs, Symbol)
    if lhs == rhs:
        return encode(isinstance(φ, Eq))
    elif lhs.compare(rhs) <= 0:
        return φ
    else:
        return φ.func(rhs, lhs)


def cmp(φ: Eq | Ne, ψ: Eq | Ne) -> int:
    result = φ.args[0].compare(ψ.args[0])
    if result == 0:
        return φ.args[1].compare(ψ.args[1])
    else:
        return result


simplify = make_simplify(atom=simplify_atom, merge=merge, cmp=cmp)
