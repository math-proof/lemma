/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralArithmeticalEulerianPolynomial.lean -/
module

public import Def.NumberTheory.GeneralArithmeticalEulerianPolynomial
public import Mathlib.Tactic

public section

namespace MetaMathlibExt

open Polynomial

example : generalArithmeticalEulerianNumber ℤ 2 0 0 1 = 1 := by
  norm_num [generalArithmeticalEulerianNumber, Finset.sum_range_succ]

example : generalArithmeticalEulerianNumber ℤ 2 1 0 1 = 1 := by
  norm_num [generalArithmeticalEulerianNumber, Finset.sum_range_succ]

example : generalArithmeticalEulerianPolynomial ℤ 2 0 1 = 1 + X := by
  norm_num [generalArithmeticalEulerianPolynomial, generalArithmeticalEulerianNumber,
    Finset.sum_range_succ]

#print axioms generalArithmeticalEulerianNumber
#print axioms generalArithmeticalEulerianPolynomial

end MetaMathlibExt
