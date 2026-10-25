/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexCyclicNeg_zero {N : Nat} (hN : 0 < N) :
    sixVertexCyclicNeg hN (⟨0, hN⟩ : Fin N) = ⟨0, hN⟩ := by
  simp [sixVertexCyclicNeg]

theorem sixVertexCyclicNeg_val_of_ne_zero
    {N : Nat} (hN : 0 < N) (i : Fin N) (hi : i.val ≠ 0) :
    (sixVertexCyclicNeg hN i).val = N - i.val := by
  simp [sixVertexCyclicNeg, hi]

theorem sixVertexCyclicNeg_involutive {N : Nat} (hN : 0 < N) :
    Function.Involutive (sixVertexCyclicNeg hN) := by
  intro i
  by_cases hi : i.val = 0
  · have hieq : i = ⟨0, hN⟩ := Fin.ext hi
    subst i
    simp
  · have hval := sixVertexCyclicNeg_val_of_ne_zero hN i hi
    have hneg0 : (sixVertexCyclicNeg hN i).val ≠ 0 := by
      rw [hval]
      omega
    apply Fin.ext
    rw [sixVertexCyclicNeg_val_of_ne_zero hN _ hneg0, hval]
    omega

end
end StatMech.FrontierD
