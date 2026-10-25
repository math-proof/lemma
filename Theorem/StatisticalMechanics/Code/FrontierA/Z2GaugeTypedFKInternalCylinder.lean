/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem mem_cubicalInternalCentralSheet_iff
    (N m : Nat) (hNm : N <= m)
    (i j : Fin (oddCubeSide m)) (f : Fin (oddCubeSide m + 1)) :
    CubicalPlaquette.xy i j f ∈ cubicalInternalCentralSheet N m hNm ↔
      m <= i.val ∧ i.val < m + N ∧
      m <= j.val ∧ j.val < m + N ∧ f.val = m := by
  constructor
  · intro hp
    obtain ⟨ij, _, heq⟩ := Finset.mem_image.mp hp
    simp only [CubicalPlaquette.xy.injEq] at heq
    have hi := congrArg Fin.val heq.1.symm
    have hj := congrArg Fin.val heq.2.1.symm
    have hf := congrArg Fin.val heq.2.2.symm
    simp only at hi hj hf
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨hi0, hi1, hj0, hj1, hf⟩
    let x : Fin N := ⟨i.val - m, by omega⟩
    let y : Fin N := ⟨j.val - m, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_univ _, ?_⟩
    rw [CubicalPlaquette.xy.injEq]
    constructor
    · apply Fin.ext
      dsimp [x]
      omega
    constructor
    · apply Fin.ext
      dsimp [y]
      omega
    · apply Fin.ext
      exact hf.symm


end
end StatMech.FrontierA
