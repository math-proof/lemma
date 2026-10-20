import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isReduced_subscheme_of_forall_isRadical'
  {X : (Scheme : Type (u + 1))} (I : X.IdealSheafData)
  (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) :
  IsReduced I.subscheme := by
  have hcov : TopologicalSpace.IsOpenCover fun U : X.affineOpens => (TopologicalSpace.Opens.map I.subschemeι.base).obj (U : X.Opens) := by
    rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    rfl
  have hX : ∀ U : X.affineOpens, IsReduced ((I.subscheme.openCoverOfIsOpenCover _ hcov).X U) := fun U => by
    let W : I.subscheme.Opens := (TopologicalSpace.Opens.map I.subschemeι.base).obj (U : X.Opens)
    let S : (Scheme : Type (u + 1)) := ↑W
    change IsReduced S
    have : IsAffine S := U.2.preimage I.subschemeι
    have hred : _root_.IsReduced ((X.presheaf.obj (Opposite.op (U : X.Opens))) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    have : _root_.IsReduced (S.presheaf.obj (Opposite.op (⊤ : S.Opens))) :=
      isReduced_of_injective (W.topIso.hom ≫ (I.subschemeObjIso U).hom).hom
        (ConcreteCategory.bijective_of_isIso _).1
    apply isReduced_of_isAffine_isReduced
  apply IsReduced.of_openCover _ (I.subscheme.openCoverOfIsOpenCover _ hcov)
/--
[AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (Z : TopologicalSpace.Closeds X) :
  -- imply
  IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  isReduced_subscheme_of_forall_isRadical' _ fun U => by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_ideal]
    apply PrimeSpectrum.isRadical_vanishingIdeal


-- created on 2026-10-20
