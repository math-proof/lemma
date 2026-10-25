/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Def.StatisticalMechanics.Code.Universality.HexNoFullSweepClose.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hexSweep_stripWinding_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) :
    (hexSweep_stripWinding inRegion a h0 z B).H = B.H := rfl


theorem hexSweep_bound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - B.H| < 6 :=
  hexJordan_bound inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B) ts hadm


end StatMech.Universality
