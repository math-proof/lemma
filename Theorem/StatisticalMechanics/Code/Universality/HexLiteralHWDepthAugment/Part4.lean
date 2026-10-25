/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_entryTurn_legal (d : HexReturnCoord) :
    hlhda_entryTurn d = 1 ∨ hlhda_entryTurn d = -1 := by
  unfold hlhda_entryTurn
  split <;> simp

theorem hlhda_entryTurn_dir {d : HexReturnCoord} (hd : HLHDAInwardDir d) :
    HexReturnCoord.base.turn (hlhda_entryTurn d) = d := by
  rcases hd with hd | hd
  · rw [hd]
    simp [hlhda_entryTurn]
  · rw [hd]
    simp [hlhda_entryTurn, HexReturnCoord.turn, HexReturnCoord.base,
      HexReturnCoord.left, HexReturnCoord.right]


end
end StatMech.Universality
