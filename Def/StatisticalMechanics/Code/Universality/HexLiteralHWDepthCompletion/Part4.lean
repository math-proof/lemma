/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part4


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_decodeCompletedPair
    (p : List ℤ × List ℤ) : List ℤ :=
  hlhda_decodePair (hlhda_eraseCompletion p)

end
end StatMech.Universality
