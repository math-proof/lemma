import Mathlib.Algebra.BigOperators.Intervals
import sympy.Basic
open Finset


@[main]
private lemma main
  [AddCommMonoid α]
  {n m : ℕ}
  {t : ℕ → ℕ}
-- given
  (h₀ : n ≤ m)
  (h₁ : Monotone t)
  (f : ℕ → α) :
-- imply
  ∑ k ∈ Ico n m, ∑ i ∈ Ico (t k) (t (k + 1)), f i = ∑ i ∈ Ico (t n) (t m), f i := by
-- proof
  induction m, h₀ using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [sum_Ico_succ_top hm, ih, sum_Ico_consecutive _ (h₁ hm) (h₁ m.le_succ)]


-- created on 2026-09-26