import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {B : Set β}
  {p : α → β → Prop}
  {x : α}
-- given
  (h : ∀ x ∈ A, ∀ y ∈ B, p x y) :
-- imply
  ∀ y ∈ B, x ∉ A ∨ p x y := by
-- proof
  intro y hy
  by_cases hx : x ∈ A
  ·
    exact Or.inr (h x hx y hy)
  ·
    exact Or.inl hx


-- created on 2018-12-19
