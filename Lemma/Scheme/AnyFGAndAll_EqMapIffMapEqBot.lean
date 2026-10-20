import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot.lean)
-/
@[path]
private lemma main
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (ι : Z ⟶ Spec (CommRingCat.of S))
    [IsClosedImmersion ι] [LocallyOfFinitePresentation ι] :
    ∃ J : Ideal S, J.FG ∧ ∀ (R : Type u) [CommRing R] (φ : S →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔ J.map φ = ⊥ := by
  obtain ⟨I, e, hι⟩ := (IsClosedImmersion.Spec_iff (f := ι)).mp inferInstance
  have hlfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :
      Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (CommRingCat.of S)) := by
    have : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = e.inv ≫ ι := by
      rw [hι, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hfp : (Ideal.Quotient.mk I).FinitePresentation := by
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)
      (φ := CommRingCat.ofHom (Ideal.Quotient.mk I))).mp hlfp
    simpa using this
  let _ : Algebra.FinitePresentation S (S ⧸ I) := by
    rw [← RingHom.finitePresentation_algebraMap, Ideal.Quotient.algebraMap_eq]; exact hfp
  have hFG : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ S I) (Ideal.Quotient.mkₐ_surjective S I)
    rwa [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] at h
  refine ⟨I, hFG, fun R _ φ => ?_⟩
  rw [Ideal.map_eq_bot_iff_le_ker]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ e.hom)
    have hc : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ) = Spec.map (CommRingCat.ofHom φ) := by
      rw [Spec.map_comp, hψ, Category.assoc, ← hι, hy]
    have hc' := Spec.map_injective hc
    intro a ha
    have : φ a = ψ.hom (Ideal.Quotient.mk I a) := by
      have := congrArg (fun k => (CommRingCat.Hom.hom k) a) hc'
      simpa using this.symm
    rw [RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro hle
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ fun a ha => hle ha)) ≫ e.inv, ?_⟩
    rw [hι, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1


-- created on 2026-10-20
