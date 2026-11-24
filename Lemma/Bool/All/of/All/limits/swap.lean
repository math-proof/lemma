import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ x ∈ A, ∀ y ∈ B, f x y) :
-- imply
  ∀ y ∈ B, ∀ x ∈ A, f x y :=
-- proof
  fun y hy x hx => h x hx y hy




-- created on 2024-06-25
-- updated on 2026-11-24
