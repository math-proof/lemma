import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (hf : lim [x → x₀] f x = A)
  (hg : lim [x → x₀] g x = B) :
-- imply
  lim [x → x₀] (f x * g x) = A * B := by
-- proof
  apply hf.mul hg


-- created on 2023-06-19
-- updated on 2026-10-26
