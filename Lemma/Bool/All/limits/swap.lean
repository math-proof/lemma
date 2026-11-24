import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop} :
-- imply
  (∀ y ∈ B, ∀ x ∈ A, f x y) ↔ ∀ x ∈ A, ∀ y ∈ B, f x y :=
-- proof
  ⟨fun h x hx y hy => h y hy x hx, fun h y hy x hx => h x hx y hy⟩




-- created on 2026-09-27
-- updated on 2026-11-24
