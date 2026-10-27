import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℕ → ℕ}
  (x : ℕ → ℕ → ℝ) :
-- imply
  ∏ i ∈ ({0, 1, 2, 3, 4} : Finset ℕ), ∏ j ∈ Finset.range (f i), x i j
    = (∏ j ∈ Finset.range (f 0), x 0 j) * (∏ j ∈ Finset.range (f 1), x 1 j)
      * (∏ j ∈ Finset.range (f 2), x 2 j) * (∏ j ∈ Finset.range (f 3), x 3 j)
      * ∏ j ∈ Finset.range (f 4), x 4 j := by
-- proof
  simp [mul_assoc]


-- created on 2020-03-07
-- updated on 2026-10-26
