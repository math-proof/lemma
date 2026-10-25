/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part9


namespace StatMech.Onsager

theorem ons_decEdgeInteriorData_offset_mem
    (L : ℕ) (d e : ons_Dart L) {z : ons_DecMicroPoint L}
    (hz : z ∈ ons_decEdgeInteriorData L d e) :
    (z.offsetX, z.offsetY) ∈ ons_decInteriorOffsets := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  unfold ons_decEdgeInteriorData at hz
  split at hz
  · fin_cases mu <;> simp at hz
    all_goals
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decInteriorOffsets]
  · fin_cases mu <;> fin_cases nu <;> simp at hz
    all_goals
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decInteriorOffsets]

end StatMech.Onsager
