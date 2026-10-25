/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part13


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWPairIncidence {T L : ℕ} (e : HexAWIncidence T L) :
    HexAWIncidence T L :=
  if h : hexAWIsInterior e then (hexAWInteriorMate ⟨e, h⟩).1 else e

end
end StatMech.Universality
