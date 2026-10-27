import Def.Analysis.Real.Limits.Part4
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ a b : ℝ}
-- given
  (hf : lim [x → x₀] f x = a)
  (hg : lim [x → x₀] g x = b) :
-- imply
  lim [x → x₀] f x = a ∧ lim [x → x₀] g x = b := by
-- proof
  apply And.intro hf hg


-- created on 2020-04-27
