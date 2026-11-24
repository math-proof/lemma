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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part115
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

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparison_of_fullCoordinateComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt_of_fullCoordinateComparison
      hcmp_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparison_of_fullCoordinateComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt_of_fullCoordinateComparison
      hcmp_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt_of_fullPredecessorComparison
      hcmp_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt_of_fullPredecessorComparison
      hcmp_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullPredecessorComparisons
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hstrict β hβpos hβc, hdiag β hβpos hβc] with
    n hstrict_n hdiag_n
  intro v hvwedge hheight
  by_cases hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))
  · refine
      ⟨boxVertStrictSectorPredecessor3 v hvwedge hlt,
        boxVertStrictSectorPredecessor3_wedge v hvwedge hlt,
        boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt,
        hstrict_n v hvwedge hlt⟩
  · refine
      ⟨boxVertDiagonalPredecessor3 v hvwedge hheight hlt,
        boxVertDiagonalPredecessor3_wedge v hvwedge hheight hlt,
        boxVertDiagonalPredecessor3_height_lt v hvwedge hheight hlt,
        hdiag_n v hvwedge hheight hlt⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullCoordinateComparisons
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullPredecessorComparisons
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparison_of_fullCoordinateComparison
      hstrict)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparison_of_fullCoordinateComparison
      hdiag)

end Exact3D
end StatMech
