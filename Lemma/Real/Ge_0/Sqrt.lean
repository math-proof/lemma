import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (_h : x ≥ 0) :
-- imply
  √x ≥ 0 := by
-- proof
  exact Real.sqrt_nonneg x


-- created on 2023-06-20
