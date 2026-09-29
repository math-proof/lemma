import sympy.Basic


@[main]
private lemma limits.delete
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ y, ∀ x ∈ A, f x y ∨ y ∉ B) :
-- imply
  ∀ y ∈ B, ∀ x ∈ A, f x y :=
-- proof
  fun y hy x hx => (h y x hx).resolve_right (not_not.mpr hy)


-- created on 2026-09-27
