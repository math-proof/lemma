/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
import Def.Combinatorics.Enumerative.EulerianPolynomialHankel


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
