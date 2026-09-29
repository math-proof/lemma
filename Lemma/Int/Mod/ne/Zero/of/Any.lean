import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {n : ℤ}
-- given
  (h : ∃ k, n = k * 2 + 1) :
-- imply
  n % 2 ≠ 0 := by
-- proof
  obtain ⟨k, rfl⟩ := h
  omega


-- created on 2026-09-27
