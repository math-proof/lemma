import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b M : ℝ}
-- given
  (h : min a b = M) :
-- imply
  M ≤ a := by
-- proof
  exact h ▸ min_le_left a b


-- created on 2019-04-24
