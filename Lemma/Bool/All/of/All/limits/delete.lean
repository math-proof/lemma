import sympy.Basic


@[path]
private lemma main
  {p : α → β → Prop}
  {A : Set α}
  {B : Set β}
  {y : β}
-- given
  (h : ∀ x ∈ A, ∀ y ∈ B, p x y)
  (hy : y ∈ B) :
-- imply
  ∀ x ∈ A, p x y := by
-- proof
  intro x hx
  apply h x hx y hy


-- created on 2026-10-11
