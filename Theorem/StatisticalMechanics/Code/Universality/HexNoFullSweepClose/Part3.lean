/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Def.StatisticalMechanics.Code.Universality.HexNoFullSweepClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hexSweep_toSimplyConnected_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    (hexSweep_toSimplyConnected inRegion a h0 z B).H = B.H := rfl

@[simp] theorem hexSweep_toSimplyConnected_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    (hexSweep_toSimplyConnected inRegion a h0 z B).w = B.w := rfl


end StatMech.Universality
