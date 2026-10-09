import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {n : ℤ}
-- given
  (h : ∃ k, n = k * 2) :
-- imply
  n % 2 = 0 := by
-- proof
  obtain ⟨k, rfl⟩ := h
  omega


-- created on 2023-05-26
