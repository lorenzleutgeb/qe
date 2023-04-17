from logic1.firstorder.formula import Formula, And, Not
from logic1.firstorder.quantified import QuantifiedFormula
from logic1.atomlib.sympy import AtomicFormula, BinaryAtomicFormula
from sympy.polys import Poly

from util import *

def closure(τ: type[QuantifiedFormula], φ: Formula) -> Formula:
	xs = φ.get_vars().free
	for x in xs:
		φ = τ(x, φ)
	return φ

def no_alternations(τ: type, φ: Formula) -> bool:
	"""
	Assumes that φ is in prenex normal form.

	Returns true if all quantifiers in the prefix of φ are
	of type τ.

	>>> no_alternations(Ex, Ex(x, Ex(y, Eq(x = y))))
	True
	>>> no_alternations(Ex, All(x, Ex(y, Eq(x = y))))
	False
	>>> no_alternations(All, All(x, All(y, Eq(x = y))))
	True
	>>> no_alternations(Ex, All(x, All(y, Eq(x = y))))
	False
	"""
	return not isinstance(φ, QuantifiedFormula) or (isinstance(φ, τ) and no_alternations(τ, φ.arg))

def is_conjunctive(φ: Formula) -> bool:
	"""
	Assumes that φ is in prenex normal form.

	>>> is_conjunctive(Ex(x, Eq(x, x)))
	True
	>>> is_conjunctive(Ex(x, Or(Eq(x, x), Neq(x, x)))
	False
	>>> is_conjunctive(Ex(x, And(Eq(x, x), Neq(x, x)))
	True
	"""
	if isinstance(φ, AtomicFormula):
		return True
	elif isinstance(φ, QuantifiedFormula):
		return is_conjunctive(matrix(φ))
	elif isinstance(φ, Not):
		return isinstance(φ.arg, AtomicFormula)
	elif isinstance(φ, And):
		return all(map(is_conjunctive, φ.args))
	else:
		return False

def matrix(φ: Formula) -> Formula:
	"""
	Assumes that φ is in prenex normal form.

	Returns the matrix of the formula.
	"""
	return matrix(φ.arg) if isinstance(φ, QuantifiedFormula) else φ

def conjunctive_core(φ: Formula) -> list[Formula]:
	"""
	Assumes that φ is in prenex normal form, all quantifiers are existential,
	and the formula is conjunctive.
	"""
	if not is_conjunctive(φ):
		raise ValueError("φ is not conjunctive")
	φ = matrix(φ)
	return list(φ.args) if isinstance(φ, And) else [φ]

def poly(φ: BinaryAtomicFormula) -> Poly:
	result = φ.args[0].as_poly()
	if not result:
		raise NotImplementedError()
	return result