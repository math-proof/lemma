/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInteriorBlockTile_fit
    (L p k : Nat) (q : Fin k) :
    p + q.val * L + L <= cubicalInteriorBlockSide L p k := by
  have hq : q.val + 1 <= k := Nat.succ_le_iff.mpr q.isLt
  have hmul : (q.val + 1) * L <= k * L := Nat.mul_le_mul_right L hq
  calc
    p + q.val * L + L = p + (q.val + 1) * L := by ring
    _ <= p + k * L := Nat.add_le_add_left hmul p
    _ <= cubicalInteriorBlockSide L p k := by
      simp [cubicalInteriorBlockSide]

end
end StatMech.FrontierA
