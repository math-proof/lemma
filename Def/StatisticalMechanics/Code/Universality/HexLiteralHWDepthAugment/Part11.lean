/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part11


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_decodePair (p : List ℤ × List ℤ) : List ℤ := by
  classical
  exact if h : ∃ ts : List ℤ, ∃ hleg :
      (ofTurns hexAWStart 1 ts).IsLegalSAW,
      hlhda_augmentedPair ts hleg = p then Classical.choose h else []

end
end StatMech.Universality
