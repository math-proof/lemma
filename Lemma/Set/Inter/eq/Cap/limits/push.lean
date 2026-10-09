import sympy.Basic
import Mathlib


@[path]
private lemma main
  {f : ℕ → Set α}
  {i n : ℕ}
-- given
  (h : i ≤ n) :
-- imply
  (⋂ k ∈ Finset.Ico i n, f k) ∩ f n = ⋂ k ∈ Finset.Ico i (n + 1), f k := by
-- proof
  rw [Nat.Ico_succ_right_eq_insert_Ico h, Finset.set_biInter_insert, Set.inter_comm]


-- created on 2021-04-27
