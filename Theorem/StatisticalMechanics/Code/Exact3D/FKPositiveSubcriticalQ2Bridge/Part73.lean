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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part75
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostScalarBound_of_currentOnePoint
    {β H : ℝ} {n : ℕ}
    (hcurrent :
      finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
        ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {none})
    ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none := by
  rw [← finiteBoundaryGhostOnePointSource_eq_symmDiff 3 n]
  rw [← finiteBoundaryGhostCurrentOnePoint_eq_expectationJ 3 n β H]
  exact hcurrent


theorem finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_scalarBound
    {β H : ℝ} {n : ℕ}
    (hbound :
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {none})
      ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none := by
  rw [finiteBoundaryGhostCurrentOnePoint_eq_expectationJ]
  rw [finiteBoundaryGhostOnePointSource_eq_symmDiff]
  exact hbound


theorem finiteBoundaryGhostCurrentOnePoint_le_of_currentSumBound
    {β H : ℝ} {n : ℕ}
    (hbound :
      Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n)
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none := by
  rw [finiteBoundaryGhostCurrentOnePoint_eq_currentSumRatio]
  exact
    (currentSum_ratio_le_iff
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)
      (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none)).2 hbound


theorem finiteBoundaryGhostScalarBound_of_currentSumBound
    {β H : ℝ} {n : ℕ}
    (hbound :
      Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n)
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {none})
    ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none :=
  finiteBoundaryGhostScalarBound_of_currentOnePoint
    (finiteBoundaryGhostCurrentOnePoint_le_of_currentSumBound hbound)


theorem finiteBoundaryGhostCurrentSumBound_of_sourcePairBound
    {β H : ℝ} {n : ℕ}
    (hpair :
      Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n)
        (∅ : Finset (Option (FK.boxVerts 3 n)))
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (∅ : Finset (Option (FK.boxVerts 3 n)))
            (∅ : Finset (Option (FK.boxVerts 3 n)))) :
    Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)
    ≤
      (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none) *
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅ :=
  currentSum_bound_of_sourcePairSum_bound
    (Sharpness.withGhost (FK.boxGraph 3 n)) β
    (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
    (finiteBoundaryGhostOnePointSource 3 n)
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β H n x none)
    hpair


theorem finiteBoundaryGhostSourcePairBound_of_edgeCopyBound
    {β H : ℝ} {n : ℕ}
    (hcopy :
      edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n)
        (∅ : Finset (Option (FK.boxVerts 3 n)))
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (∅ : Finset (Option (FK.boxVerts 3 n)))
            (∅ : Finset (Option (FK.boxVerts 3 n)))) :
    Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))
    ≤
      (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none) *
        Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))
          (∅ : Finset (Option (FK.boxVerts 3 n))) :=
  sourcePairBound_of_edgeCopyBound
    (Sharpness.withGhost (FK.boxGraph 3 n)) β
    (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
    (finiteBoundaryGhostOnePointSource 3 n)
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β H n x none)
    hcopy


theorem finiteBoundaryGhostEdgeCopyBound_of_emptyCollapsedBound
    {β H : ℝ} {n : ℕ}
    (hcopy :
      edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (∅ : Finset (Option (FK.boxVerts 3 n)))) :
    edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))
    ≤
      (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none) *
        edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))
          (∅ : Finset (Option (FK.boxVerts 3 n))) :=
  edgeCopyBound_of_emptyCollapsedBound
    (Sharpness.withGhost (FK.boxGraph 3 n)) β
    (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
    (finiteBoundaryGhostOnePointSource 3 n)
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β H n x none)
    hcopy


theorem finiteBoundaryGhostScalarBound_of_emptyCollapsedBound
    {β H : ℝ} {n : ℕ}
    (hcopy :
      edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (∅ : Finset (Option (FK.boxVerts 3 n)))) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {none})
    ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none :=
  finiteBoundaryGhostScalarBound_of_currentSumBound
    (finiteBoundaryGhostCurrentSumBound_of_sourcePairBound
      (finiteBoundaryGhostSourcePairBound_of_edgeCopyBound
        (finiteBoundaryGhostEdgeCopyBound_of_emptyCollapsedBound hcopy)))


theorem
    finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_emptyCollapsedBound
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hcopy :
      edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
      ≤
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (∅ : Finset (Option (FK.boxVerts 3 n)))) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      finiteCurrentBoundaryTwoPointSum β n :=
  finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb'
    hβ hH
    (finiteBoundaryGhostSingletonSimonLieb_of_scalarBound
      hβ hH
      (finiteBoundaryGhostScalarBound_of_emptyCollapsedBound hcopy))


theorem finiteBoundaryGhostEdgeCopySourcePairSum_zeroField_eq_zero
    (β : ℝ) (n : ℕ) :
    edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n))) = 0 := by
  refine
    edgeCopySourcePairSum_empty_eq_zero_of_expectationJ_eq_zero
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n) ?_
  rw [finiteBoundaryGhostOnePointSource_eq_symmDiff]
  exact finiteBoundaryGhostExpectation_zeroField_eq_zero β n


theorem finiteBoundaryGhostCollapsedEdgeCopySum_zeroField_eq_zero
    (β : ℝ) (n : ℕ) :
    edgeCopySourcePairEmptyCollapsedSum
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n) = 0 := by
  rw [← edgeCopySourcePairSum_empty_eq_collapsed]
  exact finiteBoundaryGhostEdgeCopySourcePairSum_zeroField_eq_zero β n


theorem finiteBoundaryGhostCollapsedEdgeCopyBound_zeroField
    (β : ℝ) (n : ℕ) :
    edgeCopySourcePairEmptyCollapsedSum
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)
    ≤
      (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none) *
        edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) := by
  rw [finiteBoundaryGhostCollapsedEdgeCopySum_zeroField_eq_zero]
  rw [finiteBoundaryGhostSimonWeight_sum_zeroField_eq_zero]
  simp


end Exact3D
end StatMech
