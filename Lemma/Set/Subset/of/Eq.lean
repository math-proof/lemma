import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : Set ℤ}
-- given
  (h : A = B) :
-- imply
  A ⊆ B := by
-- proof
  rw [h]


-- created on 2026-09-27
