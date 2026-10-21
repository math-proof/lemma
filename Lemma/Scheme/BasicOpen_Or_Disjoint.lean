import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isIntegral_subscheme_vanishingIdeal
  {X : (Scheme : Type (u + 1))}
  (Z : Set X)
  (hZ : IsClosed Z)
  (hZ' : IsIrreducible Z) :
  IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI
  let _ : IrreducibleSpace I.subscheme := by
    have h : IsIrreducible ((I.support : TopologicalSpace.Closeds X) : Set X) := by
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      apply hZ'
    refine Subtype.irreducibleSpace h
  have hred : ∀ U : X.affineOpens, _root_.IsReduced ((X.presheaf.obj (op U.1)) ⧸ I.ideal U) := fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced, hI, Scheme.IdealSheafData.vanishingIdeal_ideal]
    apply PrimeSpectrum.isRadical_vanishingIdeal
  let _ : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    let _ := hred U
    exact inferInstanceAs (IsReduced (Spec (.of ((X.presheaf.obj (op U.1)) ⧸ I.ideal U))))
  let _ : IsReduced I.subscheme := IsReduced.of_openCover (X := I.subscheme) I.subschemeCover.openCover
  apply isIntegral_of_irreducibleSpace_of_isReduced

/--
[AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2.lean)
-/
@[path]
private lemma main
  (k : Type u) [Field k] [IsAlgClosed k]
  {X : (Scheme : Type (u + 1))}
  (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
  (Z : Set X)
  (hZ : IsClosed Z)
  (hZ' : IsIrreducible Z)
  (U : X.Opens)
  (hZU : Z ⊆ U)
  (g : (X.presheaf.obj (op U))) :
  Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI
  let _ : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal Z hZ hZ'
  have hrange : Set.range I.subschemeι.base = Z := by
    change Set.range I.subschemeι = Z
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let _ : UniversallyClosed (I.subschemeι ≫ t) := inferInstance
  have hF : IsField (I.subscheme.presheaf.obj (op ⊤)) := isField_of_universallyClosed k (I.subschemeι ≫ t)
  have hpre : ((TopologicalSpace.Opens.map I.subschemeι.base).obj U) = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    show I.subschemeι.base z ∈ U
    apply hZU (hrange ▸ Set.mem_range_self z)
  have hF' : IsField (I.subscheme.presheaf.obj (op ((TopologicalSpace.Opens.map I.subschemeι.base).obj U))) := by
    rw [hpre]
    apply hF
  let _ := hF'.toField
  have key : ((TopologicalSpace.Opens.map I.subschemeι.base).obj (X.basicOpen g)) = I.subscheme.basicOpen (I.subschemeι.app U g) :=
    Scheme.preimage_basicOpen I.subschemeι g
  if h0 : I.subschemeι.app U g = 0 then
    right
    rw [Set.disjoint_left]
    rintro z hz hzg
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    have : z' ∈ ((TopologicalSpace.Opens.map I.subschemeι.base).obj (X.basicOpen g)) := hzg
    rw [key, h0, Scheme.basicOpen_zero] at this
    apply this
  else
    left
    intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    show z' ∈ ((TopologicalSpace.Opens.map I.subschemeι.base).obj (X.basicOpen g))
    rw [key, I.subscheme.basicOpen_of_isUnit (isUnit_iff_ne_zero.mpr h0), hpre]
    trivial


-- created on 2026-10-20
