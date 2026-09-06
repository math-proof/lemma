import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : f = g) :
-- imply
  (lim [x → x₀] f x) = (lim [x → x₀] g x) := by
-- proof
  rw [h]


@[main]
private lemma inf
  [Preorder α]
  {f g : α → ℝ}
-- given
  (h : f = g) :
-- imply
  (lim [x → ∞] f x) = (lim [x → ∞] g x) := by
-- proof
  apply congrArg (fun fn : α → ℝ => lim [x → ∞] fn x)
  apply h


-- created on 2020-02-24
