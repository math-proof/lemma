import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import sympy.Basic
open Finset


@[path]
private lemma main
  {n : ℕ}
  (x : Fin n → ℝ)
  (y : ℝ)
-- given
  (h₀ : 0 < n) :
-- imply
  ∑ i, (x i - ((∑ j, x j) + y) / (n + 1)) ^ 2 +
      (y - ((∑ j, x j) + y) / (n + 1)) ^ 2 =
    ∑ i, (x i - (∑ j, x j) / n) ^ 2 +
      (n : ℝ) / (n + 1) * (y - (∑ j, x j) / n) ^ 2 := by
-- proof
  set s := ∑ j : Fin n, x j
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h₀.ne'
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hzero : ∑ i, (x i - s / n) = 0 := by
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : ∑ i, x i = s := rfl
    rw [hs]
    field_simp [hn]
    ring
  have hterm : ∀ i, x i - (s + y) / (n + 1) =
      (x i - s / n) - (y - s / n) / (n + 1) := by
    intro i
    field_simp [hn, hn1]
    ring
  have hy : y - (s + y) / (n + 1) = n * (y - s / n) / (n + 1) := by
    field_simp [hn, hn1]
    ring
  simp only [hterm, hy]
  have hsum : ∑ i, ((x i - s / n) - (y - s / n) / (n + 1)) ^ 2 =
      ∑ i, (x i - s / n) ^ 2 + n * ((y - s / n) / (n + 1)) ^ 2 := by
    set δ := (y - s / n) / (n + 1)
    simp_rw [sub_sq, sub_eq_add_neg]
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    have hconst : ∑ i : Fin n, δ ^ 2 = n * δ ^ 2 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcross : ∑ i, -(2 * (x i + -(s / n)) * δ) = 0 := by
      simp_rw [← sub_eq_add_neg]
      have hre : ∀ i, -(2 * (x i - s / n) * δ) = (-(2 * δ)) * (x i - s / n) := by
        intro i
        ring
      simp_rw [hre, ← mul_sum, hzero]
      ring
    rw [hcross, hconst, add_zero]
  rw [hsum, add_assoc]
  congr 1
  field_simp [hn1]
  ring


-- created on 2019-11-16
-- updated on 2026-10-17
