module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
public import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part4


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

def hlhdt_taggedMajorant (x : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0 else 8 * x⁻¹ * (x / hexChiE) ^ T

end
end StatMech.Universality
