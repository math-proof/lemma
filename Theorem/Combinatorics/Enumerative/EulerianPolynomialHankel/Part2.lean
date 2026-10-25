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
import Def.Combinatorics.Enumerative.EulerianPolynomialHankel.Part2


section

namespace MetaMathlibExt

theorem ehd_table_diag : ∀ m : ℕ, ehd_table m m = 1
  | 0 => rfl
  | m + 1 => by
      rw [ehd_table, ehd_table_diag m, ehd_table_vanish (show m < m + 1 by omega),
        ehd_table_vanish (show m < m + 2 by omega)]
      ring

theorem ehd_table_zero_eq_poly : ∀ m : ℕ, ehd_table m 0 = ehd_poly m
  | 0 => by norm_num [ehd_table, ehd_poly, ehd_coeff, ehd_altSum]
  | m + 1 => by
      rw [ehd_table_zero_succ, ehd_table_zero_eq_poly, ehd_poly_succ]

theorem ehd_lambda_prod_range : ∀ n : ℕ,
    (∏ j ∈ Finset.range n, ehd_lambda (j + 1)) =
      Polynomial.X ^ n * Polynomial.C ((Nat.factorial n : ℤ) ^ 2)
  | 0 => by simp
  | n + 1 => by
      rw [Finset.prod_range_succ, ehd_lambda_prod_range]
      unfold ehd_lambda
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      norm_num [map_mul, map_pow]
      ring

end MetaMathlibExt
end
