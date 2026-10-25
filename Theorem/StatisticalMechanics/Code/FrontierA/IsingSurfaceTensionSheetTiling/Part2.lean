/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling
open Finset
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem tripleTile_fit (n : Nat) (q : Fin 3) :
    q.val * tripleTileSide n + tripleTileSide n <= tripleTiledSide n := by
  calc
    q.val * tripleTileSide n + tripleTileSide n =
        (q.val + 1) * tripleTileSide n := by simp [Nat.add_mul]
    _ <= 3 * tripleTileSide n :=
      Nat.mul_le_mul_right (tripleTileSide n) (by omega)
    _ = tripleTiledSide n := by
      unfold tripleTiledSide tripleTileSide
      ring

theorem tripleTile_height_fit (n : Nat) :
    tripleCentralHeight n + tripleTileSide n <= tripleTiledSide n := by
  simp [tripleCentralHeight, tripleTileSide, tripleTiledSide]
  omega


end
end StatMech.FrontierA
