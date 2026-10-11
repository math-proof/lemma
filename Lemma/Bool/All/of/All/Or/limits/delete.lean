import Lemma.Bool.All.Or.of.All.limits.delete
open Bool


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
  apply All.Or.of.All.limits.delete h


-- created on 2026-10-11
