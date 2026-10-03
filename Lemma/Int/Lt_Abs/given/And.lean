import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℤ}
-- given
  (h : |x| < a) :
-- imply
  x < a ∧ x > -a := by
-- proof
  have ⟨h₁, h₂⟩ := abs_lt.mp h
  exact ⟨h₂, h₁⟩


-- created on 2026-10-03
