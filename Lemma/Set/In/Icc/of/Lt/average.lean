import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  (a + b) / 2 ∈ Ioo a b := by
-- proof
  constructor <;> linarith


-- created on 2019-06-21
