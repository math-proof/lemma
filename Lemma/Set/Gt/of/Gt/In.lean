import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (hgt : y < x)
  (h : y ∈ Set.Icc a b) :
-- imply
  a < x := by
-- proof
  linarith [h.1]


-- created on 2020-11-25
