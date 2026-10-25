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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part7


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

namespace HLHDTaggedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N extra : ℕ}

noncomputable def lowerImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Finset HexHWContentHalf :=
  hlhdt_contentHalfImage (hhc_Dn a h0 N) H.lower H.lower_legal
    H.lower_halfSpace

noncomputable def upperImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Finset HexHWContentHalf :=
  hlhdt_contentHalfImage (hhc_Dn a h0 N) H.upper H.upper_legal
    H.upper_halfSpace

end HLHDTaggedTwoHalfData
end
end StatMech.Universality
