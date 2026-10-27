import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x M : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : x < M) :
-- imply
  √x < √M := by
-- proof
  exact Real.sqrt_lt_sqrt h₀ h₁


-- created on 2019-06-28
