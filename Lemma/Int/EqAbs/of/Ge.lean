import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≥ y) :
-- imply
  |x - y| = x - y := by
-- proof
  exact abs_of_nonneg (sub_nonneg.mpr h)


-- created on 2019-05-25
