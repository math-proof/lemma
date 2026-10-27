import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (x : ℕ → ℝ) :
-- imply
  ∏ i ∈ ({0, 1, 2, 3, 4} : Finset ℕ), x i = x 0 * x 1 * x 2 * x 3 * x 4 := by
-- proof
  simp [mul_assoc]


-- created on 2020-03-02
-- updated on 2026-10-26
