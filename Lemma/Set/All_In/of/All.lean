import sympy.Basic


@[path]
private lemma main
  {A : Set ℝ}
  {f : ℝ → Prop}
  {g : ℝ → ℝ}
-- given
  (h : ∀ x ∈ A, f (g x)) :
-- imply
  ∀ x ∈ A, g x ∈ {y | f y} :=
-- proof
  fun x hx => h x hx


-- created on 2021-08-20
