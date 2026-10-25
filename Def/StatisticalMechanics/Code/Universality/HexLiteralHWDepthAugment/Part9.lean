/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part9


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhda_forwardEncodedDir (incoming : HexReturnCoord) (t : ℤ) :
    HexReturnCoord :=
  let d := hlha_negCoord (incoming.turn t)
  if d = hlhda_flatNeighbor then incoming else d

noncomputable def hlhda_forwardCode (incoming : HexReturnCoord)
    (xs : List ℤ) : List ℤ :=
  match xs with
  | [] => hlhda_emptySide
  | t :: us =>
      hlhda_augmentSide (hlhda_forwardEncodedDir incoming t)
        (if hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor then [] else us)

end
end StatMech.Universality
