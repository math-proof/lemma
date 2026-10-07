import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℤ}
-- given
  (h : x ∈ Ico a b) :
-- imply
  a ≤ x ∧ x ≤ b - 1 := by
-- proof
  obtain ⟨ha, hb⟩ := h
  exact ⟨ha, by omega⟩


-- created on 2026-10-03
