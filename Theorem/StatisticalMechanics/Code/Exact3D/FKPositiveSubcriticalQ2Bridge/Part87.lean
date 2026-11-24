module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part89
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_eq_sourceSectorBoundaryGhostMultiplicityCap
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap n Ω =
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorBoundaryGhostMultiplicityCap
        n Ω := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorBoundaryGhostMultiplicityCap
    finiteBoundaryGhostBoundaryGhostMultiplicitySum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  rw [Finset.mul_sum]


theorem finiteBoundaryGhostSourceSector_card_le_boundaryCrossingPairCount_sum
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
    ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
      ∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
          FK.boxBoundary 3 n w),
        (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ) := by
  classical
  calc
    ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
        ∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
            FK.boxBoundary 3 n w),
          ((finiteBoundaryGhostBoundaryCrossingSourceSector m w).card :
            ℝ) :=
      finiteBoundaryGhostSourceSector_card_le_boundaryCrossing_card_sum
        (β := β) (H := H) m hweight
    _ ≤
        ∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
            FK.boxBoundary 3 n w),
          (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro w _hw
      exact
        finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount
          m w


end Exact3D
end StatMech
