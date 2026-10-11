import sympy.integrals.integrals
import sympy.Basic


@[path]
private lemma main
  {a b c t : ℝ}
  {f : ℝ → ℝ}
-- given
  (ht : 0 < t) :
-- imply
  ∫ x in a..b, f x = ∫ x in (c + t * a)..(c + t * b), f (c + t * x) * t := by
-- proof
  sorry


-- created on 2023-04-18
