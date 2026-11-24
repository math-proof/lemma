import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.relax


@[path]
private lemma main
  [Preorder α]
  {a b : α}
  {p : α → Prop}
-- given
  (h : ∃ x ∈ Ico a b, p x) :
-- imply
  ∃ y ∈ Icc a b, p y := by
-- proof
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, Set.Ico_subset_Icc_self hx, hp⟩


-- created on 2019-02-16
-- updated on 2026-11-24
