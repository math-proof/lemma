/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part53
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData_toSourceData
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData
      n v a).toSourceData =
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
        n v a := rfl


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_fullSourceClassifiedDataWeight
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a =
      finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight β H
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData
          n v a) := by
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
    finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
  simpa [finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight] using
    (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight
      (β := β) (H := H) a.1 (v := v) a.2.2)


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_fullSourceClass_ne_twoPoint
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))
    (hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n a.1) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)) ∆
        ({some v, none} : Finset (Option (FK.boxVerts 3 n))) ≠
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  intro hclass
  exact
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_decremented_univ_source_ne_twoPoint
      a hinactive
      ((finiteBoundaryGhostDecrementedSourceWeightVertexSigma_decremented_univ_source_eq_fullSource_symmDiff
        a).trans hclass)


theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    a.2 ∈
      finiteBoundaryGhostBoundaryCrossingPairDecrementFiber a.1 v
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
          n v a) := by
  classical
  rw [finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem]
  rfl


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_currentMultiplicity_le_one_iff_decrementData_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    a.1 (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
          n v a).1 (finiteBoundaryGhostBoundaryEdge n v) = 0 := by
  exact
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_le_one_iff_target_zero
      a.1 v
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
        n v a)
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber
        a)


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_not_currentMultiplicity_le_one_iff_decrementData_pos
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    ¬ a.1 (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔
      0 <
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
          n v a).1 (finiteBoundaryGhostBoundaryEdge n v) := by
  exact
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_not_oldBoundaryGhostMultiplicity_le_one_iff_target_pos
      a.1 v
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
        n v a)
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber
        a)

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_collapsedDataWeight_of_fullSourceOnePoint
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))
    (hsrc : finiteBoundaryGhostFullSourceOnePoint n a.1) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a =
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
        (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData
          a.1 v (by simpa [finiteBoundaryGhostFullSourceOnePoint] using hsrc)
          a.2.2) := by
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
    finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
  simpa [finiteBoundaryGhostCollapsedTwoPointSourceDataWeight] using
    (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight
      (β := β) (H := H) a.1 (v := v) a.2.2)


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n Ω v := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
  refine Finset.sum_nonneg ?_
  intro m _hm
  refine Finset.sum_nonneg ?_
  intro p _hp
  exact
    finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg
      (β := β) (H := H) hβ hH m v p


theorem finiteBoundaryGhostDecrementedSourceWeightSummand_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    0 ≤ finiteBoundaryGhostDecrementedSourceWeightSummand β H n m := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightSummand
  refine Finset.sum_nonneg ?_
  intro v _hv
  refine Finset.sum_nonneg ?_
  intro p _hp
  exact
    finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg
      (β := β) (H := H) hβ hH m v p


theorem finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
      ∑ m ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightSummand β H n m := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightCutoffSum
    finiteBoundaryGhostDecrementedSourceWeightSummand
  rw [Finset.sum_comm]


theorem finiteBoundaryGhostDecrementedSourceWeightCutoffSum_mono
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {Ω Ω' : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    (hΩ : Ω ⊆ Ω') :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω ≤
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω' := by
  classical
  rw [finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
    β H n Ω]
  rw [finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
    β H n Ω']
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hΩ
      (fun m _hm _hnot =>
        finiteBoundaryGhostDecrementedSourceWeightSummand_nonneg
          (β := β) (H := H) hβ hH m)


theorem finiteBoundaryGhostDecrementedSourceWeightCutoffSum_filter_add_filter_not
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (P :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P] :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n
        (Ω.filter P) +
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n
        (Ω.filter fun m => ¬ P m) := by
  classical
  rw [finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
    β H n Ω]
  rw [finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
    β H n (Ω.filter P)]
  rw [finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
    β H n (Ω.filter fun m => ¬ P m)]
  exact
    (Finset.sum_filter_add_sum_filter_not Ω P
      (finiteBoundaryGhostDecrementedSourceWeightSummand β H n)).symm


theorem finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_filter_le_filter_not_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (P :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P]
    {A B C : ℝ}
    (hP :
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n
        (Ω.filter P) ≤ A)
    (hnot :
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n
        (Ω.filter fun m => ¬ P m) ≤ B)
    (hAB : A + B ≤ C) :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω ≤ C := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
        finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n
          (Ω.filter P) +
        finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n
          (Ω.filter fun m => ¬ P m) :=
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum_filter_add_filter_not
        β H n Ω P
    _ ≤ A + B := add_le_add hP hnot
    _ ≤ C := hAB


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_mono
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {Ω Ω' : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    (hΩ : Ω ⊆ Ω')
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n Ω' v := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hΩ
      (fun m _hm _hnot =>
        Finset.sum_nonneg
          (fun p _hp =>
            finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg
              (β := β) (H := H) hβ hH m v p))


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_add_filter_not
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P] :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter P) v +
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter fun m => ¬ P m) v := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
  exact
    (Finset.sum_filter_add_sum_filter_not Ω P
      (fun m =>
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v))).symm


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_filter_le_filter_not_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
    [DecidablePred P]
    {A B C : ℝ}
    (hP :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter P) v ≤ A)
    (hnot :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter fun m => ¬ P m) v ≤ B)
    (hAB : A + B ≤ C) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ω.filter P) v +
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ω.filter fun m => ¬ P m) v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_add_filter_not
        β H n Ω v P
    _ ≤ A + B := add_le_add hP hnot
    _ ≤ C := hAB


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_sum_eq_zero_of_weight_eq_zero
    {β H : ℝ} {n : ℕ}
    {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
          0) :
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
      (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
        β H m v) = 0 := by
  classical
  exact Finset.sum_eq_zero fun p hp =>
    finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_zero_of_weight_eq_zero
      (β := β) (H := H) hvbdry hp hweight


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_weightNonzeroCutoff
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
    finiteBoundaryGhostWeightNonzeroCutoff
  calc
    (∑ m ∈ Ω,
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v)) =
      ∑ m ∈ Ω,
        if Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              ≠ 0 then
          Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
            (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
              β H m v)
        else
          0 := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      by_cases hweight :
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
              0
      · simp [hweight]
      · have hzero :
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
                0 := by
          exact not_not.mp hweight
        simp [hweight,
          finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_sum_eq_zero_of_weight_eq_zero
            (β := β) (H := H) (v := v) hvbdry hzero]
    _ =
      ∑ m ∈ Ω.filter
        (fun m =>
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
              0),
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v) := by
      rw [Finset.sum_filter]


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_label_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → ι) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
      ∑ i : ι,
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
          β H n (Ω.filter fun m => label m = i) v := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Ω) (t := (Finset.univ : Finset ι)) (g := label)
    (fun m _hm => Finset.mem_univ (label m))
    (fun m =>
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
        (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
          β H m v))]


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_label_sum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → ι)
    {A : ι → ℝ} {C : ℝ}
    (hcase :
      ∀ i,
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
          β H n (Ω.filter fun m => label m = i) v ≤ A i)
    (hC : (∑ i, A i) ≤ C) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
      β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n Ω v =
      ∑ i : ι,
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
          β H n (Ω.filter fun m => label m = i) v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_label_sum
        β H n Ω v label
    _ ≤ ∑ i, A i :=
      Finset.sum_le_sum (fun i _hi => hcase i)
    _ ≤ C := hC


theorem finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_vertexCutoffSum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {A : FK.boxVerts 3 n → ℝ} {C : ℝ}
    (hA :
      ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
          β H n Ω v ≤ A v)
    (hC :
      (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), A v) ≤ C) :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω ≤ C := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
            β H n Ω v :=
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_boundary_sum_vertexCutoffSum
        β H n Ω
    _ ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), A v :=
      Finset.sum_le_sum (fun v hv => hA v hv)
    _ ≤ C := hC


end Exact3D
end StatMech
