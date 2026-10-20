import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma isSchemeTheoreticallyDominant_specMap_of_injective
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have hinj : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom := by
    have e : (Spec.map (CommRingCat.ofHom φ)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
      rw [← Iso.inv_comp_eq]
      exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
    have i1 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    have i2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, RingHom.coe_comp]
    exact (i1.comp hφ).comp i2
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp [Scheme.IdealSheafData.ideal_bot]
private lemma eq_of_pullback_fst_comp_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y)
    (H : pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ g₁ =
      pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ g₂) : g₁ = g₂ := by
  let _ := isSchemeTheoreticallyDominant_specMap_of_injective (algebraMap k K) (algebraMap k K).injective
  let _ : IsSchemeTheoreticallyDominant (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    inferInstance
  let _ : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from fY]
    infer_instance
  let e := equalizer.ι g₁ g₂
  let _ : IsClosedImmersion e := inferInstance
  let l := equalizer.lift _ H
  have hl : l ≫ e = pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) := equalizer.lift_ι _ _
  have hker : e.ker = ⊥ := by
    apply le_bot_iff.mp
    have := Scheme.Hom.le_ker_comp l e
    rw [hl, Scheme.Hom.ker_eq_bot (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))] at this
    exact this
  let _ : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact eq_of_epi_equalizer
/--
[AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated.lean)
-/
@[path]
private lemma main
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y) (h₁ : g₁ ≫ fY = fX) (h₂ : g₂ ≫ fY = fX)
    (H : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₁ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₁]) (by rw [Category.comp_id, Category.id_comp]) =
         pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₂ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₂]) (by rw [Category.comp_id, Category.id_comp])) :
    g₁ = g₂ := by
  apply eq_of_pullback_fst_comp_eq fX fY g₁ g₂ (K := K)
  have := congrArg (· ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))) H
  simpa only [pullback.lift_fst] using this

-- created on 2026-10-20
