/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
public import Theorem.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
public import Def.Combinatorics.Enumerative.EulerianPolynomialHankel

public section

section

namespace MetaMathlibExt

theorem ehd_coeff_zero : ∀ m : ℕ, ehd_coeff m 0 = 1
  | 0 => by norm_num [ehd_coeff, ehd_altSum]
  | m + 1 => by
      have h := ehd_altSum_succ m m (by omega)
      rw [ehd_altSum_succ_self_zero m] at h
      simp only [mul_zero, zero_add, Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at h
      unfold ehd_coeff
      simp only [Nat.sub_zero]
      rw [h]
      simpa [ehd_coeff] using ehd_coeff_zero m

end MetaMathlibExt
end
