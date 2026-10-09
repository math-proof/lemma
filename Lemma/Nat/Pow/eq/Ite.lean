import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma negativeOne
  {n : ℤ} :
-- imply
  (-1 : ℝ) ^ n = if n % 2 = 0 then 1 else -1 := by
-- proof
  split_ifs with h
  · exact Even.neg_one_zpow (Int.even_iff.mpr h)
  · exact Odd.neg_one_zpow (Int.odd_iff.mpr (by omega))


@[path]
private lemma base
  {x t : ℝ}
  {A : Set ℝ}
  [DecidablePred (· ∈ A)]
  {g h : ℝ → ℝ} :
-- imply
  (if x ∈ A then g x else h x) ^ t = if x ∈ A then g x ^ t else h x ^ t := by
-- proof
  exact apply_ite (· ^ t) _ _ _


-- created on 2020-02-29
-- updated on 2026-09-27
