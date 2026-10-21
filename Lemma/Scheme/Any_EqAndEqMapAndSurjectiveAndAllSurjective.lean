import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma surjective_appTop_hom_of_iso
  {X Y : (Scheme : Type (u + 1))} (i : X ≅ Y) :
    Function.Surjective (i.hom.appTop).hom := by
  intro y
  refine ⟨i.inv.appTop.hom y, ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

private lemma surjective_appTop_inv_of_iso
  {X Y : (Scheme : Type (u + 1))} (i : X ≅ Y) :
    Function.Surjective (i.inv.appTop).hom :=
  surjective_appTop_hom_of_iso i.symm

private lemma surjective_appTop_snd
  {B C₁ : Type u} [CommRing B] [CommRing C₁] [Algebra B C₁] (t : B) [IsLocalization.Away t C₁]
  {A P : (Scheme : Type (u + 1))} (f : A ⟶ Spec (CommRingCat.of B))
  (hΓt : Function.Surjective ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))))).appTop).hom)
  (fst : P ⟶ A) (snd : P ⟶ Spec (CommRingCat.of C₁))
  (hP : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap B C₁)))) :
    Function.Surjective (snd.appTop).hom := by
  classical
  set L := Localization.Away t
  let φ : AlgEquiv B C₁ (Localization.Away t) := IsLocalization.algEquiv (Submonoid.powers t) C₁ (Localization.Away t)
  let iC : CommRingCat.of C₁ ≅ CommRingCat.of (Localization.Away t) := φ.toRingEquiv.toCommRingCatIso
  let e₃ : Spec (CommRingCat.of C₁) ≅ Spec (CommRingCat.of (Localization.Away t)) := (Scheme.Spec.mapIso iC.op).symm
  have he₃ : e₃.hom = Spec.map iC.inv := rfl
  have hkey : Spec.map (CommRingCat.ofHom (algebraMap B C₁)) ≫ (Iso.refl _).hom = e₃.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))) := by
    rw [Iso.refl_hom, Category.comp_id, he₃, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    show algebraMap B C₁ b = φ.symm (algebraMap B (Localization.Away t) b)
    apply (φ.symm.commutes b).symm
  have hP' : IsPullback fst (snd ≫ e₃.hom) f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t)))) :=
    IsPullback.of_iso hP (Iso.refl _) (Iso.refl _) e₃ (Iso.refl _) (by simp) (by simp) (by simp) hkey
  have hsnd : snd = hP'.isoPullback.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t)))) ≫ e₃.inv := by
    rw [← Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hsnd, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  intro x
  obtain ⟨y, hy⟩ := surjective_appTop_hom_of_iso hP'.isoPullback x
  obtain ⟨z, hz⟩ := hΓt y
  obtain ⟨w, hw⟩ := surjective_appTop_inv_of_iso e₃ z
  refine ⟨w, ?_⟩
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hw, hz, hy]

/--
[AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away.lean)
-/
@[path]
private lemma main
  {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] (t₀ : B) [IsLocalization.Away t₀ C]
  {A A' : (Scheme : Type (u + 1))} (f : A ⟶ Spec (CommRingCat.of B)) (e : Spec (CommRingCat.of B) ⟶ A) (he : e ≫ f = 𝟙 _)
  (hΓ : Function.Surjective (f.appTop).hom ∧ ∀ t : B, Function.Surjective ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))))).appTop).hom)
  (f' : A' ⟶ Spec (CommRingCat.of C)) (g : A' ⟶ A)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap B C)))) :
    ∃ e' : Spec (CommRingCat.of C) ⟶ A', e' ≫ f' = 𝟙 _ ∧ e' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ e ∧ Function.Surjective (f'.appTop).hom ∧ ∀ r' : C, Function.Surjective ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))))).appTop).hom := by
  classical
  have hw : (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ e) ≫ f = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  refine ⟨hsq.lift _ _ hw, hsq.lift_snd _ _ hw, hsq.lift_fst _ _ hw, ?_, ?_⟩
  · apply surjective_appTop_snd t₀ f (hΓ.2 t₀) g f' hsq
  ·
    intro r'
    set L' := Localization.Away r'
    obtain ⟨b, hb⟩ : ∃ b : B, Associated (algebraMap B C b) r' := ⟨(IsLocalization.Away.sec t₀ r').1, IsLocalization.Away.associated_sec_fst t₀ r'⟩
    let _ : IsLocalization.Away (t₀ * b) (Localization.Away r') := IsLocalization.Away.mul_of_associated t₀ b r' hb
    have hsq1 := IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))))
    have hbig := IsPullback.paste_horiz hsq1 hsq
    have hbot : Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r'))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [hbot] at hbig
    apply surjective_appTop_snd (t₀ * b) f (hΓ.2 (t₀ * b)) _ _ hbig


-- created on 2026-10-20
