import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ} :
-- imply
  (-1 : ℝ) ^ n ∈ ({-1, 1} : Finset ℝ) := by
-- proof
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow]
    simp
  · rw [h.neg_one_zpow]
    simp


-- created on 2020-03-01
