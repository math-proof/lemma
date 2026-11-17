/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Polynomial/MorganVoycePolynomial.lean -/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Polynomial.Coeff
public import Def.RingTheory.Polynomial.MorganVoycePolynomial

public section

namespace MetaMathlibExt

example : morganVoyceCoeff 3 2 = 5 := by decide

example : morganVoyceCoeff 2 3 = 0 := by decide

example : (morganVoycePolynomial ℤ 3).coeff 2 = 5 := by
  norm_num [morganVoycePolynomial, morganVoyceCoeff, Finset.sum_range_succ]
  simp [Polynomial.coeff_one]

end MetaMathlibExt
