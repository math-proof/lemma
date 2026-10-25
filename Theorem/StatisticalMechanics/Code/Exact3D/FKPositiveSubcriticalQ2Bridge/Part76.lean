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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part78
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_tanh_mul_normalized
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n =
      Real.tanh (β * H) *
        finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n := by
  unfold finiteBoundaryGhostSimonCollapsedDenominatorProduct
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct
    finiteBoundaryGhostLocalizedBoundaryExpectationSum
  rw [finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum]
  rw [finiteBoundaryGhostSimonWeight_boundarySum_eq_tanh_mul_localizedSum]
  ring


theorem finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_finiteCurrentBoundaryTwoPointSum
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostLocalizedBoundaryExpectationSum β H n =
      finiteCurrentBoundaryTwoPointSum β n := by
  simpa [finiteBoundaryGhostLocalizedBoundaryExpectationSum] using
    finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum_of_boxGeometry
      β H n


theorem finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_currentSumRatio_sum
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostLocalizedBoundaryExpectationSum β H n =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) /
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          (∅ : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  unfold finiteBoundaryGhostLocalizedBoundaryExpectationSum
  refine Finset.sum_congr rfl ?_
  intro v _hv
  exact
    Sharpness.current_representation
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))


theorem
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_emptyCollapsedSum
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n =
      finiteCurrentBoundaryTwoPointSum β n *
        edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) := by
  unfold finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct
  rw [finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_finiteCurrentBoundaryTwoPointSum]


theorem
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n =
      finiteCurrentBoundaryTwoPointSum β n *
        (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) *
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))) := by
  rw [
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_emptyCollapsedSum]
  rw [
    edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (∅ : Finset (Option (FK.boxVerts 3 n)))]


theorem
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_currentSumRatio_sum_mul_currentSum_empty_sq
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n =
      (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) /
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          (∅ : Finset (Option (FK.boxVerts 3 n)))) *
        (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) *
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))) := by
  rw [
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_emptyCollapsedSum]
  rw [← finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_finiteCurrentBoundaryTwoPointSum]
  rw [finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_currentSumRatio_sum]
  rw [
    edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (∅ : Finset (Option (FK.boxVerts 3 n)))]


end Exact3D
end StatMech
