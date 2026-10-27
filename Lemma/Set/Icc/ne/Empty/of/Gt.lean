import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  Set.Ioo a b ≠ ∅ := by
-- proof
  exact (Set.nonempty_Ioo.mpr h).ne_empty


-- created on 2021-05-08
