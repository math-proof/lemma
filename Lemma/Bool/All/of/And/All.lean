import sympy.Basic


@[path]
private lemma main
  {A : Set α}
  {c f : α → Prop}
-- given
  (h : (∀ x ∈ A, c x → f x) ∧ ∀ x ∈ A, ¬c x → f x) :
-- imply
  ∀ x ∈ A, f x := by
-- proof
  intro x hx
  by_cases hc : c x
  ·
    exact h.1 x hx hc
  ·
    exact h.2 x hx hc


-- created on 2018-12-06
