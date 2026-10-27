import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma specMap_algebraMap
  {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] :
  Surjective (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) ∧ Flat (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) ∧ QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) := by
  refine ⟨⟨fun x => ?_⟩, ?_, inferInstance⟩
  ·
    let _ : Subsingleton ↥(Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    let _ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    obtain ⟨y⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of Ω)))
    refine ⟨y, Subsingleton.elim _ _⟩
  ·
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap F Ω).Flat
    rw [RingHom.Flat]
    apply inferInstance

private lemma helper_main
  {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {X X₀ : (Scheme : Type (u + 1))} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
  (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
  Surjective r ∧ Flat r ∧ QuasiCompact r := by
  obtain ⟨h1, h2, h3⟩ := specMap_algebraMap (F := F) (Ω := Ω)
  refine ⟨MorphismProperty.of_isPullback (P := @Surjective) hr.flip h1, MorphismProperty.of_isPullback (P := @Flat) hr.flip h2, MorphismProperty.of_isPullback (P := @QuasiCompact) hr.flip h3⟩

/--
[AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field.lean)
-/
@[path]
private lemma main
  {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {X X₀ : (Scheme : Type (u + 1))} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
  (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
  -- imply
  Surjective r ∧ Flat r ∧ QuasiCompact r :=
  helper_main r hr


-- created on 2026-10-20
