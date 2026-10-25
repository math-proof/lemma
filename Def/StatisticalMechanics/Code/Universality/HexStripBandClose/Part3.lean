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
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexJordan_stripWinding (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnected inRegion a h0 z) :
    HexStripWinding inRegion a h0 z :=
  hexUmlauf_stripWinding_of_band inRegion a h0 z (hexJordan_toStripBand inRegion a h0 z B)

end StatMech.Universality
