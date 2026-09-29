import Mathlib.Data.Nat.Factorial.DoubleFactorial
import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  n ‼ = ∏ i ∈ Finset.range ⌈(n : ℝ) / 2⌉₊, (n - 2 * i) := by
-- proof
  have ev : ∀ m : ℕ, (2 * m) ‼ = ∏ i ∈ Finset.range m, (2 * m - 2 * i) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, Nat.doubleFactorial_add_two, ih, Finset.prod_range_succ']
      rw [mul_comm]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        omega
  have od : ∀ m : ℕ, (2 * m + 1) ‼ = ∏ i ∈ Finset.range (m + 1), (2 * m + 1 - 2 * i) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, Nat.doubleFactorial_add_two, ih, Finset.prod_range_succ' _ (m + 1)]
      rw [mul_comm]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        omega
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hc : ⌈((2 * m : ℕ) : ℝ) / 2⌉₊ = m := by
      push_cast
      rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Nat.ceil_natCast]
    rw [hc, ev]
  · have hc : ⌈((2 * m + 1 : ℕ) : ℝ) / 2⌉₊ = m + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      push_cast
      constructor <;> linarith
    rw [hc, od]


@[main]
private lemma double_odd
  {n : ℕ} :
-- imply
  (n * 2 - 1) ‼ = ∏ i ∈ Finset.Ico 1 (n + 1), (2 * i - 1) := by
-- proof
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ← ih]
    cases m with
    | zero => rfl
    | succ k =>
      rw [show (k + 1 + 1) * 2 - 1 = (k + 1) * 2 - 1 + 2 by omega, Nat.doubleFactorial_add_two]
      rw [mul_comm]
      congr 1
      omega


-- created on 2026-09-27
