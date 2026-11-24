module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhd_swapColor : HexAWColor → HexAWColor
  | .black => .white
  | .white => .black

end
end StatMech.Universality
