/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part5


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredShift_left_inv (n : Nat) (hn : 0 < n) :
    Function.LeftInverse (fkIsingSquareWiredShiftInv n hn)
      (fkIsingSquareWiredShift n hn) := by
  intro i
  cases i with
  | bottom => rfl
  | west k =>
      simp only [fkIsingSquareWiredShift]
      split_ifs with hk
      · simp only [fkIsingSquareWiredShiftInv]
        congr 1
        apply Fin.ext
        exact hk.symm
      · simp only [fkIsingSquareWiredShiftInv]
        split_ifs with hlt
        · congr
          omega
        · omega
  | north k =>
      simp [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]
  | top =>
      simp only [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]
      split_ifs with hlt
      · omega
      · rfl

theorem fkIsingSquareWiredShift_right_inv (n : Nat) (hn : 0 < n) :
    Function.RightInverse (fkIsingSquareWiredShiftInv n hn)
      (fkIsingSquareWiredShift n hn) := by
  intro i
  cases i with
  | bottom => rfl
  | west k =>
      simp [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]
  | north k =>
      simp only [fkIsingSquareWiredShiftInv]
      split_ifs with hlt
      · simp only [fkIsingSquareWiredShift]
        rw [dif_neg (by omega : k.val + 1 ≠ 0)]
        congr 1
      · have hk : k.val = 2 * n - 1 := by omega
        simp only [fkIsingSquareWiredShift]
        congr 1
        apply Fin.ext
        exact hk.symm
  | top =>
      simp [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]

end
end StatMech.Universality
