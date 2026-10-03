import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {f g : α → Prop}
-- given
  (h : ∀ x ∈ A, f x ∧ g x) :
-- imply
  (∀ x ∈ A, f x) ∧ (∀ x ∈ A, g x) := by
-- proof
  constructor
  · intro x hx
    exact (h x hx).1
  · intro x hx
    exact (h x hx).2


-- created on 2026-10-03
