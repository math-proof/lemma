/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexNoFullSweepClose.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexSweep_toStripBand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    HexStripBand inRegion a h0 z :=
  hexJordan_toStripBand inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B)


def hexSweep_stripWinding (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    HexStripWinding inRegion a h0 z :=
  hexJordan_stripWinding inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B)

end StatMech.Universality
