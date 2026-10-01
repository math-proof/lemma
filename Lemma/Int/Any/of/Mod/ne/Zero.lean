import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n % 2 ≠ 0) :
-- imply
  ∃ k, n = k * 2 + 1 := by
-- proof
  exact ⟨n / 2, by omega⟩


-- created on 2026-09-27
