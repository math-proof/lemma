import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x * x < y * y) :
-- imply
  √(x * x) < √(y * y) := by
-- proof
  exact Real.sqrt_lt_sqrt (mul_self_nonneg x) h


-- created on 2019-06-30
