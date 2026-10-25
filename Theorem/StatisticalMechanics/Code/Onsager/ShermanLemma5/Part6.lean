/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part5


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_mem_mSet {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) (j : Fin n) :
    j ∈ ons_mSet e rev v ↔ v j = rev (v (ons_l e rev v)) := by
  unfold ons_mSet; simp


end StatMech.Onsager
