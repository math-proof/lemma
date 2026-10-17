import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h₀ : Finset.Ico a b ≠ ∅) :
-- imply
  a - b ≤ 0 := by
-- proof
  linarith [Finset.nonempty_Ico.mp (Finset.nonempty_iff_ne_empty.mpr h₀)]


-- created on 2026-10-11
-- updated on 2026-10-17
