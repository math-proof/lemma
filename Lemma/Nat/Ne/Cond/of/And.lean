import sympy.sets.sets
import sympy.Basic


@[path]
private lemma subst.given
  {x y : ℤ}
  {p : ℤ → Prop}
-- given
  (h₀ : x ≠ y)
  (h₁ : p 0) :
-- imply
  p (if x = y then 1 else 0) := by
-- proof
  rwa [ite_eq_right h₀]


-- created on 2019-05-03
