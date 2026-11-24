module
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
public import Abbrev.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part2


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

def hexAWReflectIncidence {T L : ℕ} (e : HexAWIncidence T L) :
    HexAWIncidence T L :=
  ⟨hexAWReflectVertex e.vtx, hexAWReflectEdge e.edge⟩

end
end StatMech.Universality
