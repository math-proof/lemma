/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourMaskOfRowMasks_apply
    (rows : Fin 4 -> Nat) (x y : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (y.val * 4 + x.val) =
      (rows y).testBit x.val := by
  let i : Fin 16 := finProdFinEquiv (m := 4) (n := 4) (y, x)
  change (Nat.ofBits _).testBit (y.val * 4 + x.val) = _
  have hval : y.val * 4 + x.val = i.val := by
    simp [i, finProdFinEquiv]
    omega
  rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
  change ((rows ((finProdFinEquiv (m := 4) (n := 4)).symm i).1).testBit
        ((finProdFinEquiv (m := 4) (n := 4)).symm i).2.val) = _
  rw [(finProdFinEquiv (m := 4) (n := 4)).symm_apply_apply]

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_zero
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit x.val =
      (rows 0).testBit x.val := by
  simpa using sixVertexFourByFourMaskOfRowMasks_apply rows x 0

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_one
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (4 + x.val) =
      (rows 1).testBit x.val := by
  simpa [Nat.add_comm] using sixVertexFourByFourMaskOfRowMasks_apply rows x 1

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_two
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (8 + x.val) =
      (rows 2).testBit x.val := by
  simpa [Nat.add_comm] using sixVertexFourByFourMaskOfRowMasks_apply rows x 2

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_three
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (12 + x.val) =
      (rows 3).testBit x.val := by
  simpa [Nat.add_comm] using sixVertexFourByFourMaskOfRowMasks_apply rows x 3

end
end StatMech.FrontierD
