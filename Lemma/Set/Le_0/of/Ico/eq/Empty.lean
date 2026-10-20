import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h₀ : Finset.Ico a b = ∅) :
-- imply
  b - a ≤ 0 := by
-- proof
  linarith [Finset.Ico_eq_empty_iff.mp h₀]


-- created on 2021-06-19
-- updated on 2026-10-17
