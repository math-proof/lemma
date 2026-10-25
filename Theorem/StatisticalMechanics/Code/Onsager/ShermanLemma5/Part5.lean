/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part4


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_mem_hitSet {E} [DecidableEq E] {n : ℕ} (e : E) (rev : E → E)
    (v : Fin n → E) (k : Fin n) :
    k ∈ ons_hitSet e rev v ↔ v k = e ∨ v k = rev e := by
  unfold ons_hitSet; simp


end StatMech.Onsager
