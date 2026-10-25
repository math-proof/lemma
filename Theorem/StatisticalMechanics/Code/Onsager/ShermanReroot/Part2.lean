/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part5
import Def.StatisticalMechanics.Code.Onsager.ShermanReroot.Part2


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]


theorem ons_rotate_eq_iterate (k : Fin n) (v : Fin n → E) :
    ons_rotate k v = ons_cyclicShift^[k.val] v := by
  rw [ons_cyclicShift_iterate_apply]
  funext j
  unfold ons_rotate
  congr 1
  apply Fin.ext
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt k.isLt]


theorem ons_loopWeight_rotate (Lambda : Matrix E E ℂ) (k : Fin n) (v : Fin n → E) :
    ons_loopWeight Lambda (ons_rotate k v) = ons_loopWeight Lambda v := by
  rw [ons_rotate_eq_iterate]
  exact ons_iterate_inv (ons_loopWeight_cyclicShift Lambda) v k.val


end StatMech.Onsager
