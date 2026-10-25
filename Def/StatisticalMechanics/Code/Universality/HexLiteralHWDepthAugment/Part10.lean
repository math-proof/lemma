/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part10


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_augmentedPair (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ × List ℤ :=
  (hlhda_prefixAugment ts hleg, hlhda_suffixAugment ts hleg)

end
end StatMech.Universality
