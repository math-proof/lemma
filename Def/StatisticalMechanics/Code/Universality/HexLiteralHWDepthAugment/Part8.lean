/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part8


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_reverseCode (xs : List ℤ) : List ℤ :=
  match xs with
  | [] => hlhda_emptySide
  | _ :: us =>
      hlhda_augmentSide
        (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir
        (loopReverse us)

end
end StatMech.Universality
