import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n t : ℕ}
  {f : ℕ → ℝ} :
-- imply
  (∏ k ∈ Finset.range n, f k) ^ t = ∏ k ∈ Finset.range n, f k ^ t := by
-- proof
  exact (Finset.prod_pow _ _ _).symm


-- created on 2020-01-31
