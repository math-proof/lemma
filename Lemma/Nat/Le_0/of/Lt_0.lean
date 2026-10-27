import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma given
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  x ≤ 0 := by
-- proof
  exact h.le


-- created on 2019-12-04
