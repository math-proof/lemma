import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (u u' : Spec (CommRingCat.of K) ⟶ X) (h : u ≫ f = u' ≫ f)
  (hpt : u.base (IsLocalRing.closedPoint K) = u'.base (IsLocalRing.closedPoint K))
  (hκ : IsIso (f.residueFieldMap (u.base (IsLocalRing.closedPoint K)))) :
  -- imply
  u = u' := by
  -- proof
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective u
  obtain ⟨⟨x', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective u'
  have hx : x = x' := by
    simpa [Scheme.SpecToEquivOfField, Scheme.fromSpecResidueField_apply] using hpt
  subst hx
  have hx0 : ((Scheme.SpecToEquivOfField K X).symm ⟨x, φ⟩).base (IsLocalRing.closedPoint K) = x := by
    simp [Scheme.SpecToEquivOfField, Scheme.fromSpecResidueField_apply]
  rw [hx0] at hκ
  have key : (Scheme.SpecToEquivOfField K Y).symm ⟨f.base x, f.residueFieldMap x ≫ φ⟩ =
      (Scheme.SpecToEquivOfField K Y).symm ⟨f.base x, f.residueFieldMap x ≫ φ'⟩ := by
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simpa [Scheme.SpecToEquivOfField] using h
  have key' := (Scheme.SpecToEquivOfField K Y).symm.injective key
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at key'
  have hφ : φ = φ' := by
    let _ := hκ
    apply (cancel_epi (f.residueFieldMap x)).mp key'
  subst hφ
  rfl


-- created on 2026-10-20
