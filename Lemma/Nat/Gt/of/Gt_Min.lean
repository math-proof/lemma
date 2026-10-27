import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : min a b > x) :
-- imply
  a > x := by
-- proof
  exact lt_of_lt_of_le h (min_le_left a b)


-- created on 2019-08-04
