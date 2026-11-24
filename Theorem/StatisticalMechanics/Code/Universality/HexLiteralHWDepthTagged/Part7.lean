module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
public import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
public import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part6


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

theorem contentPair_injective
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Function.Injective H.contentPair := by
  intro d e hpair
  apply H.pair_injective
  apply Prod.ext
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.1)
      hpair
    simpa [contentPair] using h
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.2)
      hpair
    simpa [contentPair] using h

end HLHDTaggedTwoHalfData
end
end StatMech.Universality
