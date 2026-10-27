import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isClosedImmersion_fromSpecResidueField
  {S : (Scheme : Type (u + 1))} (s : S) (hs : IsClosed ({s} : Set S)) :
  IsClosedImmersion (S.fromSpecResidueField s) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [Scheme.range_fromSpecResidueField]
  apply hs

private lemma Scheme.Hom.radical_ker_of_isReduced
  {Z S : (Scheme : Type (u + 1))} (g : Z ⟶ S) [QuasiCompact g] [IsReduced Z] :
  g.ker.radical = g.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  apply IsReduced.eq_zero _ ⟨n, hn⟩

private lemma exists_eq_comp_fromSpecResidueField_of_range_subset_aux
  {Z S : (Scheme : Type (u + 1))} [IsReduced Z] (g : Z ⟶ S) [QuasiCompact g] (s : S) (hs : IsClosed ({s} : Set S)) (hg : Set.range g.base ⊆ {s}) :
  ∃ t : Z ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = g := by
  let _ := isClosedImmersion_fromSpecResidueField s hs
  refine ⟨IsClosedImmersion.lift (S.fromSpecResidueField s) g ?_, IsClosedImmersion.lift_fac _ _ _⟩
  have h1 : (S.fromSpecResidueField s).ker ≤ Scheme.IdealSheafData.vanishingIdeal ⟨{s}, hs⟩ := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]
    apply subset_closure hx
  have h2 : Scheme.IdealSheafData.vanishingIdeal ⟨{s}, hs⟩ ≤ Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    intro x hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker] at hx
    apply hs.closure_subset_iff.mpr hg hx
  rw [Scheme.IdealSheafData.vanishingIdeal_support, Scheme.Hom.radical_ker_of_isReduced] at h2
  apply h1.trans h2

/--
[AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton.lean)
-/
@[path]
private lemma main
  {Z S : (Scheme : Type (u + 1))} [IsReduced Z] (g : Z ⟶ S) [QuasiCompact g] (s : S) (hs : IsClosed ({s} : Set S)) (hg : Set.range g.base ⊆ {s}) :
  -- imply
  ∃ t : Z ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = g :=
  exists_eq_comp_fromSpecResidueField_of_range_subset_aux g s hs hg


-- created on 2026-10-20
