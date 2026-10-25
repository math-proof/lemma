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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part77
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (v : FK.boxVerts 3 n) :
    0 ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  have hJ : ∀ e, 0 ≤ J e := by
    dsimp [J]
    exact boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH
      (fun _ => by norm_num)
  have hcouplingIn :
      ∀ e, 0 ≤
        Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n) e := by
    intro e
    unfold Sharpness.couplingIn
    by_cases he :
        Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e
    · simp [he, hJ e]
    · simp [he]
  have hcorr :
      ∀ x, 0 ≤
        Sharpness.expectationJ G β
          (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), x} :
            Finset (Option (FK.boxVerts 3 n))) := by
    intro x
    exact Sharpness.ssl_expectationJ_nonneg G β
      (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
      hβ hcouplingIn
      ({some (IsingFK.boxOrigin 3 n), x} :
        Finset (Option (FK.boxVerts 3 n)))
  have hweight :
      0 ≤ finiteBoundaryGhostSimonWeight β H n (some v) none := by
    simpa [finiteBoundaryGhostSimonWeight, G, J] using
      (Sharpness.simonWeight_nonneg G β J
        (finiteBoundaryGhostOriginalSet 3 n)
        (some (IsingFK.boxOrigin 3 n)) hβ hJ hcorr
        (some v) none)
  have hempty :
      0 ≤
        edgeCopySourcePairEmptyCollapsedSum G β J
          (∅ : Finset (Option (FK.boxVerts 3 n))) :=
    edgeCopySourcePairEmptyCollapsedSum_nonneg G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))) hβ hJ
  simpa [finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct, G, J] using
    mul_nonneg hweight hempty


theorem finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_simonWeight_pos
    {β H : ℝ} {n : ℕ} (v : FK.boxVerts 3 n)
    (hweight : 0 < finiteBoundaryGhostSimonWeight β H n (some v) none) :
    0 < finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  have hempty :
      0 <
        edgeCopySourcePairEmptyCollapsedSum G β J
          (∅ : Finset (Option (FK.boxVerts 3 n))) :=
    edgeCopySourcePairEmptyCollapsedSum_empty_pos G β J
  simpa [finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct, G, J] using
    mul_pos hweight hempty


theorem finiteBoundaryGhostLocalizedBoundaryExpectation_pos_of_positive_edgeCurrent
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (v : FK.boxVerts 3 n)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hsrc :
      Sharpness.sources (Sharpness.withGhost (FK.boxGraph 3 n))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))))
    (hweight :
      0 <
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
    0 <
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (Sharpness.couplingIn
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOriginalSet 3 n))
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))) := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  have hbaseJ : ∀ e, 0 ≤ J e := by
    dsimp [J]
    exact boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH
      (fun _ => by norm_num)
  have hcouplingIn :
      ∀ e, 0 ≤
        Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n) e := by
    intro e
    unfold Sharpness.couplingIn
    by_cases he :
        Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e
    · simp [he, hbaseJ e]
    · simp [he]
  simpa [G, J] using
    expectationJ_pos_of_positive_edgeCurrent G β
      (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))
      hβ hcouplingIn m hsrc hweight


theorem
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_boundary_current_witness
    {β H : ℝ} {n : ℕ} (hβ : 0 < β) (hH : 0 < H)
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hsrc :
      Sharpness.sources (Sharpness.withGhost (FK.boxGraph 3 n))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n))))
    (hweight :
      0 <
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
    0 < finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
  classical
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hloc :
      0 <
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) :=
    finiteBoundaryGhostLocalizedBoundaryExpectation_pos_of_positive_edgeCurrent
      (β := β) (H := H) (n := n) (le_of_lt hβ) (le_of_lt hH)
      v m hsrc hweight
  have hsimon : 0 < finiteBoundaryGhostSimonWeight β H n (some v) none := by
    rw [finiteBoundaryGhostSimonWeight_some_none_of_boundary β H n hvbdry]
    exact mul_pos (real_tanh_pos_of_pos (mul_pos hβ hH)) hloc
  exact
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_simonWeight_pos
      v hsimon


theorem finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
  unfold finiteBoundaryGhostSimonCollapsedDenominatorProduct
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
  rw [finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum]
  rw [Finset.sum_mul]


end Exact3D
end StatMech
