/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part4
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectParityBit_zero : fkRectParityBit 0 = false := by
  rfl

@[simp] theorem fkRectParityBit_two_mul (n : Nat) :
    fkRectParityBit (2 * n) = false := by
  simp [fkRectParityBit]

@[simp] theorem fkRectParityBit_two_mul_add_one (n : Nat) :
    fkRectParityBit (2 * n + 1) = true := by
  simp [fkRectParityBit]

theorem fkRectParityBit_toNat (n : Nat) :
    (fkRectParityBit n).toNat = n % 2 := by
  have hn := Nat.mod_lt n (by norm_num : 0 < 2)
  interval_cases h : n % 2 <;> simp [fkRectParityBit, h]


end
end StatMech.FrontierD
