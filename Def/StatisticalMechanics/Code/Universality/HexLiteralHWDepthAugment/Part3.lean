/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

def HLHDAInwardDir (d : HexReturnCoord) : Prop :=
  d = HexReturnCoord.base.turn 1 ∨
    d = HexReturnCoord.base.turn (-1)

def hlhda_entryTurn (d : HexReturnCoord) : ℤ :=
  if d = HexReturnCoord.base.turn 1 then 1 else -1

end
end StatMech.Universality
