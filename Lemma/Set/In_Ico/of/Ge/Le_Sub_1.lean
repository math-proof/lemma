import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℤ}
-- given
  (h : x ∈ Ico a b) :
-- imply
  a ≤ x ∧ x ≤ b - 1 := by
-- proof
  obtain ⟨ha, hb⟩ := h
  exact ⟨ha, by omega⟩


-- created on 2018-03-01
