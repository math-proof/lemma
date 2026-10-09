import sympy.Basic


@[path]
private lemma limits.delete
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ y ∈ B, ∀ x ∈ A, f x y) :
-- imply
  ∀ y, ∀ x ∈ A, f x y ∨ y ∉ B := by
-- proof
  intro y x hx
  by_cases hy : y ∈ B
  ·
    exact Or.inl (h y hy x hx)
  ·
    exact Or.inr hy


-- created on 2026-09-27
