/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hlhdt_contentHalfImage
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d)) :
    Finset HexHWContentHalf := by
  classical
  exact Finset.univ.image (fun d =>
    hlhd_contentHalf (turns d) (legal d) (halfSpace d))

end
end StatMech.Universality
