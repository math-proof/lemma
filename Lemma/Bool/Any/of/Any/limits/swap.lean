import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.swap.given


@[path]
private lemma main
  {A : Set α}
  {f : β → Prop}
  {g : α → β → Prop}
-- given
  (h : ∃ y, f y ∧ ∃ x ∈ A, g x y) :
-- imply
  ∃ x ∈ A, ∃ y, f y ∧ g x y := by
-- proof
  obtain ⟨y, hy, x, hx, hg⟩ := h
  exact ⟨x, hx, y, hy, hg⟩


-- created on 2022-01-08
-- updated on 2026-11-24
