import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

/--
[AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat.lean)
-/
@[main]
private lemma main
  {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B'] [Module.FaithfullyFlat B B']
  {T : Scheme.{u}}
  {φ' : Spec (CommRingCat.of B') ⟶ T}
-- given
  (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[B] B')) ≫ φ' = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' →ₐ[B] B' ⊗[B] B').toRingHom) ≫ φ') :
-- imply
  ∃! φ : Spec (CommRingCat.of B) ⟶ T, Spec.map (CommRingCat.ofHom (algebraMap B B')) ≫ φ = φ' := by
-- proof
  have hff : (CommRingCat.ofHom (algebraMap B B')).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap B B'))).mpr hff
  haveI := hflat
  haveI := hsurj
  haveI : EffectiveEpi (Spec.map (CommRingCat.ofHom (algebraMap B B'))) := inferInstance

  have hco : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of B')),
      g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')) = g₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')) →
      g₁ ≫ φ' = g₂ ≫ φ' := by
    intro Z g₁ g₂ hg
    have e1 : g₁ = pullback.lift g₁ g₂ hg ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have e2 : g₂ = pullback.lift g₁ g₂ hg ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
    have key : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B B'))) (Spec.map (CommRingCat.ofHom (algebraMap B B'))) ≫ φ' =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B B'))) (Spec.map (CommRingCat.ofHom (algebraMap B B'))) ≫ φ' := by
      rw [← pullbackSpecIso_hom_fst B B' B', ← pullbackSpecIso_hom_snd B B' B', Category.assoc, Category.assoc, h]
      rfl
    calc g₁ ≫ φ' = (pullback.lift g₁ g₂ hg ≫ pullback.fst _ _) ≫ φ' := by rw [← e1]
      _ = pullback.lift g₁ g₂ hg ≫ (pullback.snd _ _ ≫ φ') := by rw [Category.assoc, key]
      _ = g₂ ≫ φ' := by rw [← Category.assoc, ← e2]
  refine ⟨EffectiveEpi.desc _ φ' hco, EffectiveEpi.fac _ φ' hco, fun φ hφ => EffectiveEpi.uniq _ φ' hco φ hφ⟩


-- created on 2026-10-05
