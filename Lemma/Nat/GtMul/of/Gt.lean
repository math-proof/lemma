import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y k : ℝ}
-- given
  (h : x > y)
  (hk : k > 0) :
-- imply
  x * k > y * k := by
-- proof
  exact mul_lt_mul_of_pos_right h hk


-- created on 2019-07-23
