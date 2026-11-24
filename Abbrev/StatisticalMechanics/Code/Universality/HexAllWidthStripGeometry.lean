module
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk

noncomputable section

abbrev HexAWVertex (T L : ℕ) := {c : HexAWCoord // c ∈ hexAWVertexSet T L}


end
end StatMech.Universality
