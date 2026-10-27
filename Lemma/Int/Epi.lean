import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma PresheafedSpace.epi_of_base_surjective_of_mono_c_app
  {C : Type u} [Category C] {X Y : PresheafedSpace C} (f : X ⟶ Y)
  (h₁ : Function.Surjective f.base) (h₂ : ∀ U, Mono (f.c.app U)) :
  -- imply
  Epi f := by
  -- proof
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y => by
    rw [← (h₁ y).choose_spec]
    simpa using congrArg (fun q => q.base.hom ((h₁ y).choose)) e
  suffices hgh : gc = hc by
    subst hgh
    rfl
  refine NatTrans.ext (funext fun U => ?_)
  have key := PresheafedSpace.congr_app e U
  dsimp at key
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at key
  apply (cancel_mono (f.c.app _)).mp key

private lemma Scheme.epi_of_surjective_of_app_injective
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) [Surjective f] (h : ∀ U : Y.Opens, Function.Injective (f.app U)) :
  -- imply
  Epi f := by
  -- proof
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply CategoryTheory.Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  apply PresheafedSpace.epi_of_base_surjective_of_mono_c_app _ ‹Surjective f›.surj
  intro U
  apply ConcreteCategory.mono_of_injective (f.app (Opposite.unop U)) (h (Opposite.unop U))

private lemma isSchemeTheoreticallyDominant_specMap_of_injective
  {A B : (CommRingCat : Type (u + 1))} (φ : A ⟶ B) (hφ : Function.Injective φ) :
  -- imply
  IsSchemeTheoreticallyDominant (Spec.map φ) := by
  -- proof
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have happ : Function.Injective (Spec.map φ).appTop := by
    have h1 : (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
      rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
    rw [h1]
    intro x y hxy
    simp only [CategoryTheory.comp_apply] at hxy
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1 (hφ ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1 hxy))
  rw [(RingHom.injective_iff_ker_eq_bot _).mp happ]
  ext U : 2
  simp [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_bot]

/--
[AlgebraicGeometry_epi_specMap_of_injective_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_epi_specMap_of_injective_of_finite.lean)
-/
@[path]
private lemma main
  {A B : Type u} [CommRing A] [CommRing B] (φ : RingHom A B) (hφ : Function.Injective φ) (hfin : φ.Finite) :
  -- imply
  CategoryTheory.Epi (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) := by
  -- proof
  let _ : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨hfin.to_isIntegral.comap_surjective hφ⟩
  let _ := isSchemeTheoreticallyDominant_specMap_of_injective (CommRingCat.ofHom φ) hφ
  apply Scheme.epi_of_surjective_of_app_injective _ ((Spec.map (CommRingCat.ofHom φ)).app_injective)


-- created on 2026-10-20
