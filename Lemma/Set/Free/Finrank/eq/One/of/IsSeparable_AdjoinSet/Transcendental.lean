import Mathlib
import sympy.Basic
open IntermediateField Polynomial TensorProduct Module
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 999999


private noncomputable def kaehlerPolynomialBasis (K : Type*) [Field K] : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

noncomputable instance {K : Type*} [Field K] : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

private noncomputable def kaehlerRatFuncBasis (K : Type*) [Field K] : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

private noncomputable def kaehlerOfRatFuncTowerBasis
  {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Basis Unit F Ω[F⁄K] :=
  let _ : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerRatFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

private lemma kaehlerRankOne_of_ratFuncTower
  {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
  ⟨Module.Free.of_basis (kaehlerOfRatFuncTowerBasis (K := K)),
    (Module.finrank_eq_card_basis (kaehlerOfRatFuncTowerBasis (K := K))).trans (by simp)⟩

private lemma kaehlerRankOne_of_transcendental
  [Field K] [Field F] [Algebra K F]
  {x : F}
-- given
  (htr : Transcendental K x)
  (hsep : Algebra.IsSeparable K⟮x⟯ F) :
-- imply
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
-- proof
  let _ := hsep
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  let _ : Algebra (RatFunc K) F :=
    ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
    (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K) =
    RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  let _ : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  let _ : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact kaehlerRankOne_of_ratFuncTower (K := K)

/--
[AlgebraicCurve_kaehlerRankOne_of_transcendental](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {x : F}
-- given
  (htr : Transcendental K x)
  (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
-- imply
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
-- proof
  apply kaehlerRankOne_of_transcendental htr hsep


-- created on 2026-10-20
