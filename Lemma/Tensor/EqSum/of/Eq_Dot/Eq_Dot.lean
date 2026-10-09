import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {i j : Fin n}
  {x y a b : Fin n → ℝ}
-- given
  (hy : y = fun k => x (Equiv.swap i j k))
  (hb : b = fun k => a (Equiv.swap i j k)) :
-- imply
  ∑ k, x k * a k = ∑ k, y k * b k := by
-- proof
  subst hy hb
  exact (Equiv.sum_comp (Equiv.swap i j) (fun k => x k * a k)).symm


-- created on 2019-11-13
