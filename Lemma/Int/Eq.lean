import sympy.sets.sets
import sympy.Basic


@[path]
private lemma simp.terms.negative
  {n : ℕ}
  {x y a b : Fin n → ℝ}
-- given
  (h : x - a = y - b) :
-- imply
  x + b = y + a := by
-- proof
  exact sub_eq_sub_iff_add_eq_add.mp h


-- created on 2026-09-27
