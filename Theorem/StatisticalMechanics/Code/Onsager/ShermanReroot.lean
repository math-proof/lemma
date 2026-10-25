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
import Def.StatisticalMechanics.Code.Onsager.ShermanReroot


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]


@[simp] theorem ons_rotate_apply (k j : Fin n) (v : Fin n → E) :
    ons_rotate k v j = v (j + k) := rfl

@[simp] theorem ons_rotate_zero (k : Fin n) (v : Fin n → E) :
    ons_rotate k v 0 = v k := by
  simp [ons_rotate]


end StatMech.Onsager
