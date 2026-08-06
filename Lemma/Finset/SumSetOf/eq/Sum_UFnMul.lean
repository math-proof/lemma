import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
  {a : ℤ}
-- given
  (ha : a ≠ 0)
  (s : Finset ℤ)
  (h : ℤ → ℝ)
  (f : ℤ → α) :
-- imply
  ∑ m ∈ {n ∈ s | h n > 0}.image (fun n => a * n), f m = ∑ n ∈ {n ∈ s | h n > 0}, f (a * n) := by
-- proof
  rw [Finset.sum_image]
  intro _ _ _ _ hxy
  exact mul_left_cancel₀ ha hxy


-- created on 2018-05-01
-- updated on 2026-08-06
