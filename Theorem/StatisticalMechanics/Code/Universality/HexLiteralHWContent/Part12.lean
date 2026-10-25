/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


@[simp] theorem hhc_retagBridge_width (b : HexBridge) (T : ℕ) (hT : 0 < T) :
    (hhc_retagBridge b T hT).width = T := rfl

@[simp] theorem hhc_retagBridge_content (b : HexBridge) (T : ℕ) (hT : 0 < T) :
    (hhc_retagBridge b T hT).content = b.content := rfl


theorem hhc_same_content_distinct_widths (b : HexBridge) :
    ∃ b₁ b₂ : HexBridge,
      b₁.content = b₂.content ∧ b₁.width ≠ b₂.width := by
  refine ⟨hhc_retagBridge b 1 one_pos, hhc_retagBridge b 2 (by omega), rfl, ?_⟩
  simp

end StatMech.Universality
