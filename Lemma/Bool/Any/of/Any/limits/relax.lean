import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.swap.given


@[path]
private lemma main
  [Preorder α]
  {a b : α}
  {p : α → Prop}
-- given
  (h : ∃ x ∈ Ico a b, p x) :
-- imply
  ∃ x ∈ Icc a b, p x := by
-- proof
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, Set.Ico_subset_Icc_self hx, hp⟩




-- created on 2026-09-27
-- updated on 2026-11-24
