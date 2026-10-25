/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part4
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInternalCentralUpperVertices_eq_coordinate
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    cubicalInternalCentralUpperVertices N m hNm =
      cubicalInternalCentralUpperCoordinateVertices N m hNm := by
  let zBelow : Fin (oddCubeSide m) :=
    ⟨m - 1, by dsimp [oddCubeSide]; omega⟩
  let zAbove : Fin (oddCubeSide m) :=
    ⟨m, by dsimp [oddCubeSide]; omega⟩
  let face : Fin (oddCubeSide m + 1) :=
    ⟨m, by dsimp [oddCubeSide]; omega⟩
  have hback : finBackward face = some zBelow := by
    rw [finBackward_eq_some_iff]
    apply Fin.ext
    dsimp [face, zBelow]
    omega
  have hforward : finForward face = some zAbove := by
    rw [finForward_eq_some_iff]
    apply Fin.ext
    rfl
  unfold cubicalInternalCentralUpperVertices typedMarkedBondVertices
    cubicalInternalCentralSheet cubicalInternalCentralUpperCoordinateVertices
  rw [Finset.image_image]
  apply Finset.image_congr
  intro ij _
  simp [typedFalseEndpoint, cubicalDualEnds, face, hback, hforward,
    cubicalInternalCentralBlockSpin, zBelow, zAbove]
  omega


end
end StatMech.FrontierA
