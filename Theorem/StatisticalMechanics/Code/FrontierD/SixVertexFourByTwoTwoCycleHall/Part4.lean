/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoArrowsOf_encodedMasks
    (omega : SixVertexArrows sixVertexFourByTwoTorus) :
    sixVertexFourByTwoArrowsOfMasks
        (sixVertexFourByTwoHorizontalMask omega)
        (sixVertexFourByTwoVerticalMask omega) = omega := by
  apply SixVertexArrows.ext
  · funext v
    let i : Fin 8 := finProdFinEquiv (m := 2) (n := 4) (v.2, v.1)
    change (Nat.ofBits _).testBit (v.2.val * 4 + v.1.val) = _
    have hval : v.2.val * 4 + v.1.val = i.val := by
      simp [i, finProdFinEquiv]
      omega
    rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
    change omega.horizontal
      ((finProdFinEquiv (m := 2) (n := 4)).symm i).swap =
        omega.horizontal v
    rw [(finProdFinEquiv (m := 2) (n := 4)).symm_apply_apply]
    rfl
  · funext v
    let i : Fin 8 := finProdFinEquiv (m := 2) (n := 4) (v.2, v.1)
    change (Nat.ofBits _).testBit (v.2.val * 4 + v.1.val) = _
    have hval : v.2.val * 4 + v.1.val = i.val := by
      simp [i, finProdFinEquiv]
      omega
    rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
    change omega.vertical
      ((finProdFinEquiv (m := 2) (n := 4)).symm i).swap =
        omega.vertical v
    rw [(finProdFinEquiv (m := 2) (n := 4)).symm_apply_apply]
    rfl

end
end StatMech.FrontierD
