/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part11


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWInteriorIncidences (T L : ℕ) : Finset (HexAWIncidence T L) :=
  (hexAWIncidences T L).filter hexAWIsInterior


def hexAWBoundaryIncidences (T L : ℕ) : Finset (HexAWIncidence T L) :=
  hexAWIncidences T L \ hexAWInteriorIncidences T L

end
end StatMech.Universality
