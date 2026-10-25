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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part105
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def boxVertDiagonalPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    FK.boxVerts 3 n :=
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  boxVertOfCoords3 n (n : ℤ) (y - 1) z
    (by simp)
    (by
      have hy_nonneg : 0 ≤ y := by
        simpa [y] using hvwedge.2.1
      have hy_le_z : y ≤ z := by
        simpa [y, z] using hvwedge.2.2
      have hy_ne_zero : y ≠ 0 := by
        intro hy0
        have hz0 : z = 0 := by omega
        apply hheight
        simp [boxVertTransverseHeight3, y, z, hy0, hz0]
      have hym_nonneg : 0 ≤ y - 1 := by omega
      have hym_lt_y : (y - 1).natAbs < y.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt hym_nonneg (by omega)
      have hy_bound : y.natAbs ≤ n := by
        simpa [y] using v.property (1 : Fin 3)
      exact le_trans (Nat.le_of_lt hym_lt_y) hy_bound)
    (by simpa [z] using v.property (2 : Fin 3))

end Exact3D
end StatMech
