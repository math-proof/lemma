/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part7


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourVerticalMaskOfRows_apply
    (rows : Fin 4 -> SixVertexRow 4) (x y : Fin 4) :
    (sixVertexFourByFourVerticalMaskOfRows rows).testBit (y.val * 4 + x.val) =
      rows y x := by
  let i : Fin 16 := finProdFinEquiv (m := 4) (n := 4) (y, x)
  change (Nat.ofBits _).testBit (y.val * 4 + x.val) = _
  have hval : y.val * 4 + x.val = i.val := by
    simp [i, finProdFinEquiv]
    omega
  rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
  change rows ((finProdFinEquiv (m := 4) (n := 4)).symm i).1
      ((finProdFinEquiv (m := 4) (n := 4)).symm i).2 = _
  rw [(finProdFinEquiv (m := 4) (n := 4)).symm_apply_apply]

end
end StatMech.FrontierD
