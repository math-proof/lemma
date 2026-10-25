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
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]


def ons_rotateEquiv (k : Fin n) : (Fin n → E) ≃ (Fin n → E) where
  toFun := ons_rotate k
  invFun := ons_rotate (-k)
  left_inv v := by
    funext j
    simp [ons_rotate, add_assoc]
  right_inv v := by
    funext j
    simp [ons_rotate, add_assoc]

end StatMech.Onsager
