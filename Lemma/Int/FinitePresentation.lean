import Mathlib
import sympy.Basic


/--
[Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C] [Module.Finite R C] [Module.Flat R C] :
-- imply
  Algebra.FinitePresentation R C := by
-- proof
  have : Module.Free R C := Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  exact Algebra.FinitePresentation.of_finitePresentation R C


-- created on 2026-10-03
