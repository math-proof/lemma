import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {i j : Fin n}
  {x y : Fin n → ℝ}
-- given
  (hy : y = fun k => x (Equiv.swap i j k)) :
-- imply
  ∑ k, x k = ∑ k, y k := by
-- proof
  subst hy
  exact (Equiv.sum_comp (Equiv.swap i j) x).symm


-- created on 2026-09-27
