module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
public import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

namespace HLHDTaggedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N extra : ℕ}

noncomputable def pairImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Finset (HexHWContentHalf × HexHWContentHalf) := by
  classical
  exact Finset.univ.image H.contentPair

end HLHDTaggedTwoHalfData
end
end StatMech.Universality
