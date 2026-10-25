/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexNoFullSweepClose.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexSweep_toSimplyConnected (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    HexStripSimplyConnected inRegion a h0 z where
  H := B.H
  w := B.w
  hHL := B.hHL
  hHU := B.hHU
  hh0L := B.hh0L
  hh0U := B.hh0U
  wall := B.wall
  attainsWall := B.attainsWall
  noFullSweep := fun ts hadm i j hi hj hsweep => B.noFullSweepField ts hadm i j hi hj hsweep

end StatMech.Universality
