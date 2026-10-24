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
import sympy.atlas.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
section
namespace MetaMathlibExt

/-! # Hankel transform of Eulerian polynomials
-/

private def ehd_altSum (m q : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (q + 1),
    (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) * ((q - i : ℕ) : ℤ) ^ m

private def ehd_coeff (m k : ℕ) : ℤ :=
  ehd_altSum m (m - k)

private noncomputable def ehd_poly (m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (ehd_coeff m k)

private theorem ehd_coeff_zero : ∀ m : ℕ, ehd_coeff m 0 = 1
  | 0 => by norm_num [ehd_coeff, ehd_altSum]
  | m + 1 => by
      have h := ehd_altSum_succ m m (by omega)
      rw [ehd_altSum_succ_self_zero m] at h
      simp only [mul_zero, zero_add, Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at h
      unfold ehd_coeff
      simp only [Nat.sub_zero]
      rw [h]
      simpa [ehd_coeff] using ehd_coeff_zero m

private noncomputable def ehd_b (k : ℕ) : Polynomial ℤ :=
  Polynomial.C (k + 1 : ℤ) + Polynomial.C (k : ℤ) * Polynomial.X

private noncomputable def ehd_lambda (k : ℕ) : Polynomial ℤ :=
  Polynomial.C ((k : ℤ) ^ 2) * Polynomial.X

private noncomputable def ehd_table : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => ehd_table m 0 + Polynomial.X * ehd_table m 1
  | m + 1, k + 1 =>
      ehd_table m k + ehd_b (k + 1) * ehd_table m (k + 1) +
        ehd_lambda (k + 2) * ehd_table m (k + 2)

private theorem ehd_table_diag : ∀ m : ℕ, ehd_table m m = 1
  | 0 => rfl
  | m + 1 => by
      rw [ehd_table, ehd_table_diag m, ehd_table_vanish (show m < m + 1 by omega),
        ehd_table_vanish (show m < m + 2 by omega)]
      ring

private theorem ehd_table_zero_eq_poly : ∀ m : ℕ, ehd_table m 0 = ehd_poly m
  | 0 => by norm_num [ehd_table, ehd_poly, ehd_coeff, ehd_altSum]
  | m + 1 => by
      rw [ehd_table_zero_succ, ehd_table_zero_eq_poly, ehd_poly_succ]

private theorem ehd_lambda_prod_range : ∀ n : ℕ,
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
