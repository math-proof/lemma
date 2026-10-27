import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  x + |x| ≥ 0 := by
-- proof
  linarith [neg_abs_le x]


-- created on 2019-09-15
