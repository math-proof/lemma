import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_moduleFinite_globalSections_of_isProper_of_isAffineHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_moduleFinite_globalSections_of_isProper_of_isAffineHom.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R))
  [IsProper f] [IsAffineHom f] :
  -- imply
  let _ : Algebra R (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  Module.Finite R (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) := by
  -- proof
  let _ : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  let _ : IsAffine X := isAffine_of_isAffineHom f
  have hfin : f.appTop.hom.Finite := Scheme.Hom.finite_appTop f
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  have hcomp : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.Finite := by
    rw [CommRingCat.hom_comp]
    apply hfin.comp (RingHom.Finite.of_surjective _ hsurj)
  refine hcomp


-- created on 2026-10-20
