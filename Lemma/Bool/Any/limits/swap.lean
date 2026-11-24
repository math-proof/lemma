import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.limits.domain_defined


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop} :
-- imply
  (∃ y ∈ B, ∃ x ∈ A, f x y) ↔ ∃ x ∈ A, ∃ y ∈ B, f x y :=
-- proof
  ⟨fun ⟨y, hy, x, hx, h⟩ => ⟨x, hx, y, hy, h⟩, fun ⟨x, hx, y, hy, h⟩ => ⟨y, hy, x, hx, h⟩⟩




-- created on 2026-09-27
-- updated on 2026-11-24
