import Def.Analysis.Real.Limits.Part4
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ A : ℝ}
-- given
  (h : lim [x → x₀] f x = A) :
-- imply
  lim [x → x₀] f x = A := by
-- proof
  apply h


-- created on 2020-04-26
