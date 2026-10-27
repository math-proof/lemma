import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma of_affine
  {X Y Z : (Scheme : Type (u + 1))} [IsAffine X] [IsAffine Y] [IsAffine Z]
  {f : X ⟶ Y} {g : Y ⟶ Z} (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
  LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  apply RingHom.FinitePresentation.of_comp_finiteType _ h hg

private lemma of_affine_target
  {X Y Z : (Scheme : Type (u + 1))} [IsAffine Y] [IsAffine Z]
  {f : X ⟶ Y} {g : Y ⟶ Z} (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
  LocallyOfFinitePresentation f := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_affineOpens_eq_top X)]
  intro U
  have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation U.1.ι (f ≫ g) h
  rw [← Category.assoc] at H
  apply of_affine H hg

private lemma of_affine_base
  {X Y Z : (Scheme : Type (u + 1))} [IsAffine Z]
  {f : X ⟶ Y} {g : Y ⟶ Z} (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
  LocallyOfFinitePresentation f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_affineOpens_eq_top Y)]
  intro U
  have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
    (Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U.1 : X.Opens)) (f ≫ g) h
  rw [← morphismRestrict_ι_assoc] at H
  apply of_affine_target H (HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFiniteType U.1.ι g hg)

/--
[AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType.lean)
-/
@[path]
private lemma main
  {X Y Z : (Scheme : Type (u + 1))} {f : X ⟶ Y} {g : Y ⟶ Z} (h : LocallyOfFinitePresentation (f ≫ g))
  (hg : LocallyOfFiniteType g) :
  -- imply
  LocallyOfFinitePresentation f := by
  -- proof
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
  intro U
  have H := IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation) h U.1
  rw [morphismRestrict_comp] at H
  apply of_affine_base H (IsZariskiLocalAtTarget.restrict (P := @LocallyOfFiniteType) hg U.1)


-- created on 2026-10-20
