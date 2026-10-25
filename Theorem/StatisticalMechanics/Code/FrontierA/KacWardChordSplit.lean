/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal
import Def.StatisticalMechanics.Code.FrontierA.KacWardChordSplit


namespace StatMech.FrontierA

theorem kwChordPrefixIndex_injective {n : ℕ} [NeZero n] (j : Fin n) :
    Function.Injective (kwChordPrefixIndex j) := by
  intro k l h
  apply Fin.ext
  simpa [kwChordPrefixIndex] using congrArg Fin.val h

@[simp] theorem kwChordPrefixIndex_zero {n : ℕ} [NeZero n]
    (j : Fin n) : kwChordPrefixIndex j 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem kwChordPrefixIndex_last {n : ℕ} [NeZero n]
    (j : Fin n) : kwChordPrefixIndex j (Fin.last j.val) = j := by
  apply Fin.ext
  simp [kwChordPrefixIndex]

theorem kwChordPrefixIndex_castSucc_add_one {n : ℕ} [NeZero n]
    (j : Fin n) (q : Fin j.val) :
    kwChordPrefixIndex j (q.castSucc + 1) =
      kwChordPrefixIndex j q.castSucc + 1 := by
  apply Fin.ext
  have hprefix : q.val + 1 < j.val + 1 := by omega
  have hold : q.val + 1 < n := lt_of_lt_of_le hprefix
    (Nat.succ_le_iff.mpr j.isLt)
  simp [kwChordPrefixIndex, Fin.val_add, Nat.mod_eq_of_lt hprefix,
    Nat.mod_eq_of_lt hold]

@[simp] theorem kwChordPrefixIndex_last_add_one {n : ℕ} [NeZero n]
    (j : Fin n) :
    kwChordPrefixIndex j (Fin.last j.val + 1) = 0 := by
  apply Fin.ext
  simp [kwChordPrefixIndex, Fin.val_add]


end StatMech.FrontierA
