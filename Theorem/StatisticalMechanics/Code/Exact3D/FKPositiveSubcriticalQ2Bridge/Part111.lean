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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part113
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt_of_fullCoordinateComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt
      β hβpos n := by
  intro v hvwedge hlt
  rcases hcmp v hvwedge hlt with ⟨w, hwcoords, hprob⟩
  have hcanon :
      boxVertHasCoords3
        (boxVertStrictSectorPredecessor3 v hvwedge hlt) (n : ℤ)
        ((v : Lattice.Site 3) (1 : Fin 3))
        (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
    simp
  calc
    freeQ2DoubledFullOriginConnProb β hβpos n v
        ≤ freeQ2DoubledFullOriginConnProb β hβpos n w := hprob
    _ =
        freeQ2DoubledFullOriginConnProb β hβpos n
          (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
      freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
        hwcoords hcanon

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt_of_fullCoordinateComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt
      β hβpos n := by
  intro v hvwedge hheight hnotlt
  rcases hcmp v hvwedge hheight hnotlt with ⟨w, hwcoords, hprob⟩
  have hcanon :
      boxVertHasCoords3
        (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) (n : ℤ)
        (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
        ((v : Lattice.Site 3) (2 : Fin 3)) := by
    simp
  calc
    freeQ2DoubledFullOriginConnProb β hβpos n v
        ≤ freeQ2DoubledFullOriginConnProb β hβpos n w := hprob
    _ =
        freeQ2DoubledFullOriginConnProb β hβpos n
          (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) :=
      freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
        hwcoords hcanon

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt_of_fullPredecessorComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt
      β hβpos n := by
  intro v hvwedge hlt
  refine
    ⟨boxVertStrictSectorPredecessor3 v hvwedge hlt, by simp,
      hcmp v hvwedge hlt⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt_of_fullPredecessorComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt
      β hβpos n := by
  intro v hvwedge hheight hnotlt
  refine
    ⟨boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt, by simp,
      hcmp v hvwedge hheight hnotlt⟩

end Exact3D
end StatMech
