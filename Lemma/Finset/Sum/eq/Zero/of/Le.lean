import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  {f : ℤ → ℤ}
-- given
  (h : b ≤ a) :
-- imply
  ∑ n ∈ Finset.Ico a b, f n = 0 := by
-- proof
  rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]


-- created on 2019-11-18
