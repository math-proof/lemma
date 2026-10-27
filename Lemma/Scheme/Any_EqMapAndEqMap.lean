import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_comp_eq_and_comp_eq_of_valuationSubring_comap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_and_comp_eq_of_valuationSubring_comap.lean)
-/
@[path]
private lemma main
  {Ω K' : Type u} [Field Ω] [Field K'] (φ : RingHom K' Ω) (A : ValuationSubring Ω)
  {X : (Scheme : Type (u + 1))} (x : Spec (CommRingCat.of K') ⟶ X) (y : Spec (CommRingCat.of ↥A) ⟶ X)
  (hxy : Spec.map (CommRingCat.ofHom A.subtype) ≫ y = Spec.map (CommRingCat.ofHom φ) ≫ x) :
  -- imply
  ∃ z : Spec (CommRingCat.of (A.comap φ).toSubring) ⟶ X, Spec.map (CommRingCat.ofHom (A.comap φ).subtype) ≫ z = x ∧ Spec.map (CommRingCat.ofHom ((φ.comp (A.comap φ).subtype).codRestrict A.toSubring (fun r => r.2))) ≫ z = y := by
  -- proof
  classical
  set ιA : CommRingCat.of ↥A ⟶ CommRingCat.of Ω := CommRingCat.ofHom A.subtype with hιA
  set φ' : CommRingCat.of K' ⟶ CommRingCat.of Ω := CommRingCat.ofHom φ with hφ'
  have hpt : (Spec.map φ') (IsLocalRing.closedPoint (CommRingCat.of Ω)) = IsLocalRing.closedPoint (CommRingCat.of K') := Subsingleton.elim _ _
  have hη : x (IsLocalRing.closedPoint (CommRingCat.of K')) = y ((Spec.map ιA) (IsLocalRing.closedPoint (CommRingCat.of Ω))) := by
    rw [← hpt, ← Scheme.Hom.comp_apply, ← hxy, Scheme.Hom.comp_apply]
  have h : x (IsLocalRing.closedPoint (CommRingCat.of K')) ⤳ y (IsLocalRing.closedPoint (CommRingCat.of ↥A)) := by
    rw [hη]
    apply (IsLocalRing.specializes_closedPoint _).map y.continuous
  set f := Scheme.stalkClosedPointTo y with hf
  set g₀ := X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo x with hg₀
  have key : g₀ ≫ φ' = f ≫ ιA := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk _)]
    simp only [hg₀, hf, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk, ← hxy]
    congr 1
    apply (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm
  have key' : ∀ s, φ (g₀.hom s) = ((f.hom s : ↥A) : Ω) := fun s => by
    have := congrArg (fun k => k.hom s) key
    simpa [hφ', hιA] using this
  let f' : RingHom (X.presheaf.stalk (y (IsLocalRing.closedPoint (CommRingCat.of ↥A)))) (A.comap φ).toSubring :=
    g₀.hom.codRestrict (A.comap φ) (fun s => ValuationSubring.mem_comap.mpr (by rw [key']; apply (f.hom s).2))
  refine ⟨Spec.map (CommRingCat.ofHom f') ≫ X.fromSpecStalk _, ?_, ?_⟩
  ·
    have e1 : CommRingCat.ofHom f' ≫ CommRingCat.ofHom (A.comap φ).subtype = g₀ := by
      ext s
      rfl
    rw [← Spec.map_comp_assoc, e1, hg₀, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  ·
    have e2 : CommRingCat.ofHom f' ≫ CommRingCat.ofHom ((φ.comp (A.comap φ).subtype).codRestrict A.toSubring (fun r => r.2)) = f := by
      ext s
      apply key' s
    rw [← Spec.map_comp_assoc, e2, hf]
    apply Scheme.Spec_stalkClosedPointTo_fromSpecStalk y


-- created on 2026-10-20
