import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ a b : ℝ}
-- given
  (_ : a ≠ 0)
  (hf : lim [x → x₀] f x = a)
  (hg : lim [x → x₀] g x = b) :
-- imply
  lim [x → x₀] (f x * g x) = a * b := by
-- proof
  apply hf.mul hg


-- created on 2020-04-16
-- updated on 2026-10-26
