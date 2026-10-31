import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ b : ℝ}
-- given
  (hf : lim [x → x₀] f x = 0)
  (hg : lim [x → x₀] g x = b) :
-- imply
  lim [x → x₀] (f x * g x) = 0 := by
-- proof
  simpa using hf.mul hg


-- created on 2020-04-10
-- updated on 2026-10-26
