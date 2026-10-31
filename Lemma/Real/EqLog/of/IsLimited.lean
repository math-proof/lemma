import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic
open Set Real


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x₀ y : ℝ}
-- given
  (h : lim [x → x₀] g x = y)
  (hy : y ∈ Ioi 0) :
-- imply
  lim [x → x₀] Real.log (g x) = Real.log y := by
-- proof
  apply (continuousAt_log (ne_of_gt (mem_Ioi.mp hy))).tendsto.comp h


-- created on 2020-06-19
