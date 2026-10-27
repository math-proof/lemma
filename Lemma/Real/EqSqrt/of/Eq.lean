import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  √x = √y := by
-- proof
  rw [h]


-- created on 2020-06-10
