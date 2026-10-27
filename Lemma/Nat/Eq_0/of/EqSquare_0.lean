import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma complex
  {x : ℂ}
-- given
  (h : x ^ 2 = 0) :
-- imply
  x = 0 := by
-- proof
  exact (pow_eq_zero_iff two_ne_zero).mp h


-- created on 2018-11-11
