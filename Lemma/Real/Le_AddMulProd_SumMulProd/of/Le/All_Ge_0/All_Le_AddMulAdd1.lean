import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import sympy.Basic
open Finset


@[main]
private lemma main
  {u b c : ℕ → ℝ}
  {n₀ n : ℕ}
-- given
  (h₀ : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (h₁ : ∀ n ≥ n₀, c n ≥ 0)
  (h₂ : n₀ ≤ n) :
-- imply
  u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) + ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) := by
-- proof
  induction n, h₂ using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    calc
      _ ≤ (1 + c k) * u k + b k := h₀ k hk
      _ ≤ (1 + c k) * (u n₀ * ∏ i ∈ Ico n₀ k, (1 + c i) + ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, (1 + c i)) + b k := by
        have := h₁ k hk
        gcongr
      _ = _ := by
        have hs : ∀ j ∈ Ico n₀ k, (1 + c k) * (b j * ∏ i ∈ Ico (j + 1) k, (1 + c i)) = b j * ∏ i ∈ Ico (j + 1) (k + 1), (1 + c i) := fun j hj => by
          rw [prod_Ico_succ_top (by grind)]
          ring
        rw [prod_Ico_succ_top hk, sum_Ico_succ_top hk, Ico_self, prod_empty, mul_one, mul_add, mul_sum, sum_congr rfl hs]
        ring


-- created on 2026-09-26