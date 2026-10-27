import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b)
  (x : ℝ) :
-- imply
  max a x = max b x := by
-- proof
  rw [h]


-- created on 2021-08-07
