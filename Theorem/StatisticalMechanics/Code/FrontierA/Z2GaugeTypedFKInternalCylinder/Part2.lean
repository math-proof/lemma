/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part2
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInternalCentralSheet_subset_cut
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    cubicalInternalCentralSheet N m hNm ⊆
      multibondCut
        (cubicalDualEnds
          (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m))
        (cubicalInternalCentralBlockSpin N m) := by
  intro p hp
  obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hp
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
  rw [mem_multibondCut]
  simp [cubicalDualEnds, face, hback, hforward,
    cubicalInternalCentralBlockSpin, zBelow, zAbove]
  omega


end
end StatMech.FrontierA
