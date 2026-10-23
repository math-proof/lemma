import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Lemma.P2M.Util

open AlgebraicCurve
open scoped Pointwise

/--
[AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul.lean)
-/

private lemma  restrictAlong_algEquiv
    {K F : Type*}
    [Field K]
    [Field F]
    [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral)
    (w : Place K F) :
    w.restrictAlong (σ : F →ₐ[K] F) hσ = (SemilinearAut.ofAlgAut σ)⁻¹ • w := by
  let := AlgebraicCurve.algebraAlong (σ : F →ₐ[K] F)
  have := AlgebraicCurve.isScalarTower_along (σ : F →ₐ[K] F)
  have : Algebra.IsIntegral F F := AlgebraicCurve.isIntegral_along _ hσ
  show w.restrict F = (SemilinearAut.ofAlgAut σ)⁻¹ • w
  apply Place.ext
  rw [Place.restrict_toValuationSubring, SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_inv_pointwise_smul_iff,
    SemilinearAut.ofAlgAut_smul]
  exact Iff.rfl

private lemma  ramificationIndexAlong_algEquiv
    {K F : Type*}
    [Field K]
    [Field F]
    [Algebra K F]
    [HasPrincipalDivisors K F] (σ : F ≃ₐ[K] F)
    (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (w : Place K F) :
    Place.ramificationIndexAlong (σ : F →ₐ[K] F) w = 1 := by
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible ((SemilinearAut.ofAlgAut σ)⁻¹ • w).toValuationSubring
  have h1 : ((SemilinearAut.ofAlgAut σ)⁻¹ • w).ord (π : F) = 1 :=
    ((SemilinearAut.ofAlgAut σ)⁻¹ • w).ord_coe_irreducible hπ
  have h2 : w.ord (σ (π : F)) = 1 := by
    have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) ((SemilinearAut.ofAlgAut σ)⁻¹ • w) (π : F)
    rw [smul_inv_smul, SemilinearAut.ofAlgAut_smul] at h
    rw [h, h1]
  have h3 := Place.ord_restrictAlong (σ : F →ₐ[K] F) hσ w (π : F)
  rw [restrictAlong_algEquiv, h1, mul_one, AlgEquiv.coe_toAlgHom, h2] at h3
  exact_mod_cast h3.symm


open AlgebraicCurve in
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
  {D : AlgebraicCurve.Divisor K F}
-- given
  (σ : F ≃ₐ[K] F)
  (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) :
-- imply
  AlgebraicCurve.Divisor.pullbackAlong (σ : F →ₐ[K] F) hσ D = AlgebraicCurve.SemilinearAut.ofAlgAut σ • D := by
-- proof
  ext w
  rw [Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    ramificationIndexAlong_algEquiv σ hσ, restrictAlong_algEquiv, Nat.cast_one, one_mul]


-- created on 2026-10-23
