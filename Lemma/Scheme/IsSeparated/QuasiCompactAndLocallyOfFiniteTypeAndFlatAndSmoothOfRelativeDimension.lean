import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma _root_.AlgebraicGeometry.Scheme.Opens.quasiCompact_ι_of_isClosed
  {X : (Scheme : Type (u + 1))} (U : X.Opens)
  (hU : IsClosed (U : Set X)) :
  QuasiCompact U.ι := by
  constructor
  intro V _ hV
  rw [U.ι.isOpenEmbedding.isInducing.isCompact_iff, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  exact hV.inter_right hU
/--
[AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] {X : (Scheme : Type (u + 1))} (πX : X ⟶ Spec (CommRingCat.of B))
  (U : X.Opens) (hU : IsClosed (U : Set X)) :
  -- imply
  (IsSeparated πX → IsSeparated (U.ι ≫ πX)) ∧ (QuasiCompact πX → QuasiCompact (U.ι ≫ πX)) ∧
    (LocallyOfFiniteType πX → LocallyOfFiniteType (U.ι ≫ πX)) ∧ (Flat πX → Flat (U.ι ≫ πX)) ∧
    (SmoothOfRelativeDimension 1 πX → SmoothOfRelativeDimension 1 (U.ι ≫ πX)) := by
  -- proof
  let _ : QuasiCompact U.ι := U.quasiCompact_ι_of_isClosed hU
  refine ⟨fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, fun _ => ?_⟩
  refine inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ πX))


-- created on 2026-10-20
