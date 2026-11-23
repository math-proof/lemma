/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/TrinomialTransformSequence.lean -/
module

public import Def.NumberTheory.TrinomialTransformSequence
public import Theorem.Nat.TrinomialTransformSequence
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.NormNum

public section

namespace MetaMathlibExt

example : trinomialTransformSequence (R := ℕ) (fun k => k) 0 = 0 := by
  simpa using trinomialTransformSequence_zero (R := ℕ) (fun k => k)

example : trinomialTransformSequence (R := ℕ) (fun k => k) 1 = 3 := by
  norm_num [trinomialTransformSequence, trinomialCoefficient, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    Finset.sum_range_succ]

example : trinomialTransformSequence (R := ℤ) (fun _ => 0) 17 = 0 := by
  exact trinomialTransformSequence_zero_apply 17

end MetaMathlibExt
