import Mathlib
import sympy.Basic

open IntermediateField Polynomial

/--
[AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional.lean)
-/
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {x : F}
-- given
  (htr : Transcendental K x)
  (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
-- imply
  Algebra.EssFiniteType K F := by
-- proof
  have := hfd
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  have : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  have : Algebra.EssFiniteType K (RatFunc K) := Algebra.EssFiniteType.comp K K[X] (RatFunc K)
  have : Algebra.EssFiniteType K ↥K⟮x⟯ := Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  have : Algebra.EssFiniteType ↥K⟮x⟯ F := Algebra.EssFiniteType.of_finiteType _ _
  exact Algebra.EssFiniteType.comp K ↥K⟮x⟯ F


-- created on 2026-10-05
