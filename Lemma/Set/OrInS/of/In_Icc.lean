import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x a b c : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  x ∈ Ico a c ∨ x ∈ Icc c b := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  obtain hxc | hcx := lt_or_ge x c
  · left
    exact ⟨hax, hxc⟩
  · right
    exact ⟨hcx, hxb⟩


-- created on 2020-04-12
-- updated on 2026-10-26
