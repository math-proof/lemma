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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part103
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def boxVertStrictSectorPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    FK.boxVerts 3 n :=
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  boxVertOfCoords3 n (n : ℤ) y (z - 1)
    (by simp)
    (by simpa [y] using v.property (1 : Fin 3))
    (by
      have hz_minus_nonneg : 0 ≤ z - 1 := by
        have hy_nonneg : 0 ≤ y := by
          simpa [y] using hvwedge.2.1
        omega
      have hzm_lt_z : (z - 1).natAbs < z.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt hz_minus_nonneg (by omega)
      have hz_bound : z.natAbs ≤ n := by
        simpa [z] using v.property (2 : Fin 3)
      exact le_trans (Nat.le_of_lt hzm_lt_z) hz_bound)

end Exact3D
end StatMech
