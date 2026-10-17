import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic
open Finset


@[path]
private lemma main
  {n : ℕ}
  (x : Fin n → ℝ)
-- given
  (h₀ : 0 < n) :
-- imply
  ∑ i, ∑ j, (x i - x j) ^ 2 =
    2 * (n : ℝ) * ∑ i, (x i - (∑ j, x j) / n) ^ 2 := by
-- proof
  set s := ∑ j : Fin n, x j
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h₀.ne'
  have hconst : ∀ a : ℝ, ∑ j : Fin n, a = n * a := by
    intro a
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hexp : ∀ i j, (x i - x j) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * x i * x j := by
    intro i j
    ring
  have hpair : ∑ i, ∑ j, (x i - x j) ^ 2 =
      2 * (n : ℝ) * ∑ i, x i ^ 2 - 2 * s ^ 2 := by
    simp_rw [hexp, sum_sub_distrib, sum_add_distrib]
    simp_rw [hconst]
    have hcross : ∑ i, ∑ j, 2 * x i * x j = 2 * s ^ 2 := by
      have hinner : ∀ i, ∑ j, 2 * x i * x j = (2 * x i) * s := by
        intro i
        rw [mul_sum]
      simp_rw [hinner]
      rw [← sum_mul, ← mul_sum]
      have hs : ∑ i, x i = s := rfl
      rw [hs]
      ring
    have hpull : ∑ i, (n : ℝ) * x i ^ 2 = n * ∑ i, x i ^ 2 := by
      rw [mul_sum]
    rw [hcross, hpull]
    ring
  have hvar : ∑ i, (x i - s / n) ^ 2 = ∑ i, x i ^ 2 - s ^ 2 / n := by
    have hv : ∀ i, (x i - s / n) ^ 2 = x i ^ 2 - 2 * x i * (s / n) + (s / n) ^ 2 := by
      intro i
      ring
    simp_rw [hv, sum_add_distrib, sum_sub_distrib]
    simp_rw [hconst]
    have hlin : ∑ i, 2 * x i * (s / n) = 2 * (s / n) * s := by
      have hre : ∀ i, 2 * x i * (s / n) = (2 * (s / n)) * x i := by
        intro i
        ring
      rw [sum_congr rfl fun i _ => hre i, mul_sum]
    rw [hlin]
    field_simp [hn]
    ring
  rw [hpair, hvar]
  field_simp [hn]


-- created on 2019-11-15
-- updated on 2026-10-17
