import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≥ y) :
-- imply
  ⌊x⌋ ≥ ⌊y⌋ := by
-- proof
  exact Int.floor_mono h


-- created on 2021-12-27
