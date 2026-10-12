import Mathlib
import sympy.Basic


attribute [local instance] Ideal.Quotient.field


/--
[Algebra_Etale_of_isReduced_of_perfectField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_of_isReduced_of_perfectField.lean)
-/
@[path]
private lemma main
  [Field K] [PerfectField K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] :
-- imply
  Algebra.Etale K B := by
-- proof
  have : IsArtinianRing B := .of_finite K B
  have hfe : Algebra.FormallyEtale K B := by
    have hI (I : MaximalSpectrum B) : Algebra.FormallyEtale K (B ⧸ I.asIdeal) := by
      have : I.asIdeal.IsMaximal := I.isMaximal
      have : Module.Finite K (B ⧸ I.asIdeal) := Module.Finite.quotient K _
      have : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
      have : Algebra.IsSeparable K (B ⧸ I.asIdeal) := inferInstance
      apply Algebra.FormallyEtale.of_isSeparable K (B ⧸ I.asIdeal)
    apply Algebra.FormallyEtale.of_equiv ((IsArtinianRing.equivPi B).restrictScalars K).symm
  have : Algebra.FiniteType K B := inferInstance
  apply Algebra.Etale.mk hfe (Algebra.FinitePresentation.of_finiteType.mp inferInstance)


-- created on 2026-10-12
