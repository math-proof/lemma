/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part5


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 1000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorZeroMasks_classify
    (horizontalMask : Fin 256)
    (verticalMask : SixVertexFourByTwoVerticalMaskInSector 0)
    (hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val).IceRule)
    :
    exists i : Fin 4,
      sixVertexFourByTwoSectorZeroMasks i =
        (horizontalMask.val, verticalMask.val.val) := by
  decide +revert

set_option maxHeartbeats 1000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorOneMasks_classify
    (horizontalMask : Fin 256)
    (verticalMask : SixVertexFourByTwoVerticalMaskInSector 1)
    (hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val).IceRule) :
    exists i : Fin 28,
      sixVertexFourByTwoSectorOneMasks i =
        (horizontalMask.val, verticalMask.val.val) := by
  decide +revert

set_option maxHeartbeats 1000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorTwoMasks_classify
    (horizontalMask : Fin 256)
    (verticalMask : SixVertexFourByTwoVerticalMaskInSector 2)
    (hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val).IceRule) :
    exists i : Fin 50,
      sixVertexFourByTwoSectorTwoMasks i =
        (horizontalMask.val, verticalMask.val.val) := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorZeroArrows_injective :
    Function.Injective sixVertexFourByTwoSectorZeroArrows := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorOneArrows_injective :
    Function.Injective sixVertexFourByTwoSectorOneArrows := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorTwoArrows_injective :
    Function.Injective sixVertexFourByTwoSectorTwoArrows := by
  decide +revert

theorem sixVertexFourByTwoSectorZeroConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorZeroConfiguration := by
  intro i j hij
  apply sixVertexFourByTwoSectorZeroArrows_injective
  exact congrArg Subtype.val hij

theorem sixVertexFourByTwoSectorOneConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorOneConfiguration := by
  intro i j hij
  apply sixVertexFourByTwoSectorOneArrows_injective
  exact congrArg Subtype.val hij

theorem sixVertexFourByTwoSectorTwoConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorTwoConfiguration := by
  intro i j hij
  apply sixVertexFourByTwoSectorTwoArrows_injective
  exact congrArg Subtype.val hij

theorem sixVertexFourByTwoSectorZeroConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorZeroConfiguration := by
  intro omega
  let horizontalMask := sixVertexFourByTwoHorizontalMaskFin omega.1
  let verticalMask := sixVertexFourByTwoVerticalMaskInSector 0
    omega.1 omega.2.2
  have hencoded := sixVertexFourByTwoArrowsOf_encodedMasks omega.1
  have hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val.val).IceRule := by
    change (sixVertexFourByTwoArrowsOfMasks
      (sixVertexFourByTwoHorizontalMask omega.1)
      (sixVertexFourByTwoVerticalMask omega.1)).IceRule
    rw [hencoded]
    exact omega.2.1
  obtain ⟨i, hmasks⟩ :=
    sixVertexFourByTwoSectorZeroMasks_classify
      horizontalMask verticalMask hice
  refine ⟨i, Subtype.ext ?_⟩
  change sixVertexFourByTwoSectorZeroArrows i = omega.1
  unfold sixVertexFourByTwoSectorZeroArrows
  rw [hmasks]
  exact hencoded

theorem sixVertexFourByTwoSectorOneConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorOneConfiguration := by
  intro omega
  let horizontalMask := sixVertexFourByTwoHorizontalMaskFin omega.1
  let verticalMask := sixVertexFourByTwoVerticalMaskInSector 1
    omega.1 omega.2.2
  have hencoded := sixVertexFourByTwoArrowsOf_encodedMasks omega.1
  have hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val.val).IceRule := by
    change (sixVertexFourByTwoArrowsOfMasks
      (sixVertexFourByTwoHorizontalMask omega.1)
      (sixVertexFourByTwoVerticalMask omega.1)).IceRule
    rw [hencoded]
    exact omega.2.1
  obtain ⟨i, hmasks⟩ :=
    sixVertexFourByTwoSectorOneMasks_classify
      horizontalMask verticalMask hice
  refine ⟨i, Subtype.ext ?_⟩
  change sixVertexFourByTwoSectorOneArrows i = omega.1
  unfold sixVertexFourByTwoSectorOneArrows
  rw [hmasks]
  exact hencoded

theorem sixVertexFourByTwoSectorTwoConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorTwoConfiguration := by
  intro omega
  let horizontalMask := sixVertexFourByTwoHorizontalMaskFin omega.1
  let verticalMask := sixVertexFourByTwoVerticalMaskInSector 2
    omega.1 omega.2.2
  have hencoded := sixVertexFourByTwoArrowsOf_encodedMasks omega.1
  have hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val.val).IceRule := by
    change (sixVertexFourByTwoArrowsOfMasks
      (sixVertexFourByTwoHorizontalMask omega.1)
      (sixVertexFourByTwoVerticalMask omega.1)).IceRule
    rw [hencoded]
    exact omega.2.1
  obtain ⟨i, hmasks⟩ :=
    sixVertexFourByTwoSectorTwoMasks_classify
      horizontalMask verticalMask hice
  refine ⟨i, Subtype.ext ?_⟩
  change sixVertexFourByTwoSectorTwoArrows i = omega.1
  unfold sixVertexFourByTwoSectorTwoArrows
  rw [hmasks]
  exact hencoded

end
end StatMech.FrontierD
