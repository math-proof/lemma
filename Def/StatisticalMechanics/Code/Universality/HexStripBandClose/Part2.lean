/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexJordan_toStripBand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    HexStripBand inRegion a h0 z where
  H := B.H
  w := B.w
  hHL := B.hHL
  hHU := B.hHU
  hh0L := B.hh0L
  hh0U := B.hh0U
  wall := fun ts hadm k hk => B.wallField ts hadm k hk
  noFullTurn := fun ts hadm k hk => B.noFullTurnField ts hadm k hk

end StatMech.Universality
