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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part112
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
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt_of_predecessorComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorPredecessorComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt
      β hβpos n := by
  intro v hvwedge
  dsimp only
  intro hlt
  refine ⟨boxVertStrictSectorPredecessor3 v hvwedge hlt, ?_, ?_⟩
  · simp
  · exact hcmp v hvwedge hlt


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt_of_predecessorComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalPredecessorComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt
      β hβpos n := by
  intro v hvwedge hheight
  dsimp only
  intro hnotlt
  refine ⟨boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt, ?_, ?_⟩
  · simp
  · exact hcmp v hvwedge hheight hnotlt


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStep_of_predecessorComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt_of_predecessorComparison
      hcmp_n


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStep_of_predecessorComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt_of_predecessorComparison
      hcmp_n


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_predecessorComparisons
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStep_of_predecessorComparison
      hstrict)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStep_of_predecessorComparison
      hdiag)

end Exact3D
end StatMech
