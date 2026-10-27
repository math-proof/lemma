import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  {a : ℤ}
-- given
  (h : ⌊x⌋ = a) :
-- imply
  x ∈ Set.Ico (a : ℝ) ((a : ℝ) + 1) := by
-- proof
  exact Int.floor_eq_iff.mp h


-- created on 2023-05-29
