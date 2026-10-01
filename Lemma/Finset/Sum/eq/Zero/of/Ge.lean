import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  {f : ℤ → ℤ}
-- given
  (h : a ≥ b) :
-- imply
  ∑ n ∈ Finset.Ico a b, f n = 0 := by
-- proof
  rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]


-- created on 2026-09-27
