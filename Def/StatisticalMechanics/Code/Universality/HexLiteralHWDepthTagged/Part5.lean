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
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

namespace HLHDTaggedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N extra : ℕ}

noncomputable def lowerHalf
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hlhd_contentHalf (H.lower d) (H.lower_legal d) (H.lower_halfSpace d)

noncomputable def upperHalf
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hlhd_contentHalf (H.upper d) (H.upper_legal d) (H.upper_halfSpace d)

end HLHDTaggedTwoHalfData
end
end StatMech.Universality
