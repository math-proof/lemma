import sympy.functions.combinatorial.numbers
import sympy.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
open Nat


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  (Stirling n k : ℝ) = (∑ i ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * (i : ℝ) ^ n) / (k ! : ℝ) := by
-- proof
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℝ, T = fun m k => ∑ i ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * (i : ℝ) ^ m :=
    ⟨_, rfl⟩
  have hA : ∀ m k, ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * ((j : ℝ) + 1) ^ m = T m k + T m (k + 1) := by
    intro m k
    have h₁ : T m (k + 1) = ∑ j ∈ Finset.range (k + 1), ((-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * ((j : ℝ) + 1) ^ m + (-1 : ℝ) ^ (k - j) * (k.choose (j + 1) : ℝ) * ((j : ℝ) + 1) ^ m) + (-1 : ℝ) ^ (k + 1) * (0 : ℝ) ^ m := by
      simp only [hT]
      rw [Finset.sum_range_succ']
      congr 1
      ·
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show k + 1 - (j + 1) = k - j by omega, Nat.choose_succ_succ]
        push_cast
        ring
      ·
        simp
    have h₂ : T m k = ∑ j ∈ Finset.range k, (-1 : ℝ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℝ) * ((j : ℝ) + 1) ^ m + (-1 : ℝ) ^ k * (0 : ℝ) ^ m := by
      simp only [hT]
      rw [Finset.sum_range_succ']
      congr 1
      ·
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        ring
      ·
        simp
    have h₃ : ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose (j + 1) : ℝ) * ((j : ℝ) + 1) ^ m = -∑ j ∈ Finset.range k, (-1 : ℝ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℝ) * ((j : ℝ) + 1) ^ m := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      rw [show k - j = k - (j + 1) + 1 by omega, pow_succ]
      ring
    rw [h₁, h₂, Finset.sum_add_distrib, h₃, pow_succ]
    ring
  have hZ : ∀ m k, T m k = (k ! : ℝ) * (Stirling m k : ℝ) := by
    intro m
    induction m with
    | zero =>
      intro k
      cases k with
      | zero =>
        simp [hT, Stirling, Nat.stirlingSecond_zero]
      | succ k =>
        have h := hA 0 k
        have h₀ : T 0 k = ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) := by
          simp only [hT, pow_zero, mul_one]
        simp only [pow_zero, mul_one] at h
        rw [h₀] at h
        have h' : T 0 (k + 1) = 0 := by linarith
        rw [h']
        simp [Stirling, Nat.stirlingSecond_zero_succ]
    | succ m ih =>
      intro k
      cases k with
      | zero =>
        simp [hT, Stirling, Nat.stirlingSecond_succ_zero]
      | succ k =>
        have e : T (m + 1) (k + 1) = ((k : ℝ) + 1) * ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * ((j : ℝ) + 1) ^ m := by
          simp only [hT]
          rw [Finset.sum_range_succ', Finset.mul_sum]
          simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero m), mul_zero, add_zero]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hc : ((k + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) = ((k : ℝ) + 1) * (k.choose j : ℝ) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq k j).symm
          rw [show k + 1 - (j + 1) = k - j by omega]
          push_cast
          rw [pow_succ]
          linear_combination ((-1 : ℝ) ^ (k - j) * ((j : ℝ) + 1) ^ m) * hc
        rw [e, hA, ih, ih]
        simp only [Stirling]
        rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
        push_cast
        ring
  have h := hZ n k
  simp only [hT] at h
  rw [h, mul_div_cancel_left₀ _ (by positivity)]


-- created on 2026-09-27
