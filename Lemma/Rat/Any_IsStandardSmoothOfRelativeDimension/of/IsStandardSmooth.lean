import Mathlib
import sympy.Basic


/--
[Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field.lean)
-/
@[main]
private lemma main
  [Field k] [CommRing B] [Algebra k B]
-- given
  (h : Algebra.IsStandardSmooth k B) :
-- imply
  ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k B := by
-- proof
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, ⟨ι, σ, hσ, hι, P, rfl⟩⟩


-- created on 2026-10-01
