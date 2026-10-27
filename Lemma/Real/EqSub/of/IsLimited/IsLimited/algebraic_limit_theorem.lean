import Def.Analysis.Real.Limits.Part4
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ A B : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : lim [x → x₀] g x = B) :
-- imply
  lim [x → x₀] (f x - g x) = A - B := by
-- proof
  apply h₀.sub h₁


-- created on 2020-05-18
-- updated on 2026-10-26
