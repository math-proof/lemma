/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal


namespace StatMech.FrontierA

def kwChordPrefixIndex {n : ℕ} [NeZero n] (j : Fin n) :
    Fin (j.val + 1) → Fin n :=
  fun k ↦ ⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr j.isLt)⟩

end StatMech.FrontierA
