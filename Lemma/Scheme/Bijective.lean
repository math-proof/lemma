import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma flat_of_field {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Flat f := by
  let _ : Subsingleton ↥(Spec (CommRingCat.of k)) := (inferInstance : Subsingleton (PrimeSpectrum k))
  let _ : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  infer_instance
private lemma bijective_appLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    Function.Bijective (f.appLE ⊤ ⊤ e).hom ↔ Function.Bijective f.appTop.hom := by
  rw [Scheme.Hom.appLE_congr f e rfl (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)
    (fun φ => Function.Bijective φ.hom), Scheme.Hom.appLE_eq_app]
  exact Iff.rfl
/--
[AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen.lean)
-/
@[path]
private lemma main
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fY] [IsSeparated fY]
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p₁.app U).hom := by
  let _ : Flat fX := flat_of_field fX
  let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace fY
  let _ : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated fY
  let _ : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hY
  let hfY : IsIso fY.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
  have hUSX : U ≤ fX ⁻¹ᵁ ⊤ := le_top
  have hUST : (⊤ : Y.Opens) ≤ fY ⁻¹ᵁ ⊤ := by simp
  have hUY : p₁ ⁻¹ᵁ U = p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ ⊤ := by simp
  let _ : IsIso (fY.appLE ⊤ ⊤ hUST) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((bijective_appLE_top_iff fY hUST).mpr (ConcreteCategory.bijective_of_isIso fY.appTop))
  let hps := isIso_pushoutSection_of_isQuasiSeparated_of_flat_left hP hUST hUSX hUY
    (isAffineOpen_top _) hU
    (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
    (by rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ)
  have hcomp : pushout.inl (fX.appLE ⊤ U hUSX) (fY.appLE ⊤ ⊤ hUST) ≫
      pushoutSection hP hUST hUSX hUY = p₁.appLE U (p₁ ⁻¹ᵁ U) (by simp) :=
    pushout.inl_desc _ _ _
  have hiso : IsIso (p₁.appLE U (p₁ ⁻¹ᵁ U) (by simp)) := by
    rw [← hcomp]
    infer_instance
  have := ConcreteCategory.bijective_of_isIso (p₁.appLE U (p₁ ⁻¹ᵁ U) le_rfl)
  rwa [Scheme.Hom.appLE_eq_app] at this


-- created on 2026-10-20
