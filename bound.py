
from logic1.firstorder.formula import Formula, And, Or, Not
from logic1.firstorder.quantified import All, Ex, QuantifiedFormula
from logic1.atomlib.sympy import AtomicFormula, BinaryAtomicFormula, Eq, Ne, Term, Gt, Lt, Ge, Le
from simplify import simplify
from sympy.polys import Poly

from itertools import product

from util import *

import logging

import enum

class Bound(enum.Flag):
	NONE  = 0
	LOWER = enum.auto()
	UPPER = enum.auto()

def bound(φ: BinaryAtomicFormula, x) -> Bound:
	(a, p) = (0, poly(φ))
	try:
		a = p.coeff_monomial(x)
	except ValueError:
		return Bound.NONE

	if isinstance(φ, Eq):
		return Bound.LOWER | Bound.UPPER

	return Bound.UPPER if (isinstance(φ, Lt) or isinstance(φ, Le)) == (a > 0) else Bound.LOWER

def remove_unbounded(φ: Formula) -> Formula:
	return simplify(closure(Ex, And(*remove_unbounded_list(conjunctive_core(φ)))))

def remove_unbounded_list(rows: list[BinaryAtomicFormula]) -> list[BinaryAtomicFormula]:
	upper = set([x for φ in rows for x in φ.get_vars().free if bound(φ, x) & Bound.UPPER])
	lower = set([x for φ in rows for x in φ.get_vars().free if bound(φ, x) & Bound.LOWER])

	logging.debug("Variables bounded from above are: " + str(upper))
	logging.debug("Variables bounded from below are: " + str(lower))
	keep = upper.intersection(lower)
	logging.debug("Variables to keep are: " + str(keep))
	return [φ for φ in rows if not φ.get_vars().free.difference(keep)]