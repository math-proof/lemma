import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A : Set α}
  {f : β → Prop}
  {g : α → β → Prop}
-- given
  (h : ∃ x ∈ A, ∃ y, f y ∧ g x y) :
-- imply
  ∃ y, f y ∧ ∃ x ∈ A, g x y := by
-- proof
  obtain ⟨x, hx, y, hy, hg⟩ := h
  exact ⟨y, hy, x, hx, hg⟩




-- created on 2026-09-27
-- updated on 2026-11-24
