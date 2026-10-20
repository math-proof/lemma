import sympy.Basic


@[path]
private lemma main
  {p : α → β → Prop}
  {A : Set α}
  {B : Set β}
-- given
  (h : ∀ x ∈ A, ∀ y ∈ B, p x y) :
-- imply
  ∀ y ∈ B, ∀ x, p x y ∨ x ∉ A := by
-- proof
  intro y hy x
  if hx : x ∈ A then
    left
    apply h x hx y hy
  else
    right
    apply hx


-- created on 2018-12-17
