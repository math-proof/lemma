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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part111
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_body_of_at
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepAt
        β hβpos n) :
    ∀ v : FK.boxVerts 3 n,
      boxVertPositiveXFaceOrderedWedge3 n v →
        boxVertTransverseHeight3 v ≠ 0 →
          let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
          let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
          if y < z then
            ∃ w : FK.boxVerts 3 n,
              boxVertHasCoords3 w (n : ℤ) y (z - 1) ∧
                ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                    (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                  : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                    (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                  ≤
                ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                    (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                  : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                    (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w)
          else
            ∃ w : FK.boxVerts 3 n,
              boxVertHasCoords3 w (n : ℤ) (y - 1) z ∧
                ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                    (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                  : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                    (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                  ≤
                ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                    (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                  : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                    (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w) := by
  intro v hvwedge hheight
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  by_cases hlt : y < z
  · have hcase := hstep.1 v hvwedge hlt
    simpa [freeQ2DoubledInnerOriginConnProb, y, z, hlt] using hcase
  · have hcase := hstep.2 v hvwedge hheight hlt
    simpa [freeQ2DoubledInnerOriginConnProb, y, z, hlt] using hcase


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_local
    (hlocal : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
      ∀ᶠ n in atTop,
        FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepAt
          β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hlocal β hβpos hβc] with n hstep_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_body_of_at
      hstep_n


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_local
    (fun β hβpos hβc => by
      filter_upwards [hstrict β hβpos hβc, hdiag β hβpos hβc] with
        n hstrict_n hdiag_n
      exact ⟨hstrict_n, hdiag_n⟩)


end Exact3D
end StatMech
