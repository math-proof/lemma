import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (hb : b < 0)
  (h : a = b) :
-- imply
  a < 0 := by
-- proof
  rw [h]
  exact hb


-- created on 2021-09-17
