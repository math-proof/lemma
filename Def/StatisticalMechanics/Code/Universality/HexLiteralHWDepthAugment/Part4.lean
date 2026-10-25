/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part4


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhda_augmentSide (d : HexReturnCoord) (internal : List ℤ) : List ℤ :=
  [-1, 1, hlhda_entryTurn d] ++ internal


def hlhda_emptySide : List ℤ := [-1, 1]

end
end StatMech.Universality
