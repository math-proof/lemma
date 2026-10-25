/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part7


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_suffixAugment (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ :=
  match hsuf : ts.drop (hlhda_cutPos ts hleg) with
  | [] => hlhda_emptySide
  | t :: us =>
      if hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) =
          hlhda_flatNeighbor then
        hlhda_augmentSide (hlhda_cutState ts hleg).dir []
      else
        hlhda_augmentSide
          (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us

end
end StatMech.Universality
