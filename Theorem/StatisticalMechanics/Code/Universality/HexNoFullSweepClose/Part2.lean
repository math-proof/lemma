/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Structure.StatisticalMechanics.Code.Universality.HexNoFullSweepClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexStripSimplyConnectedMonotone

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
  (B : HexStripSimplyConnectedMonotone inRegion a h0 z)

include B in


theorem noFullSweepField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (i j : ℕ) (hi : i ≤ ts.length) (hj : j ≤ ts.length)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
  rcases le_total i j with hij | hji
  · 
    have hmono := (B.monotoneSweep ts hadm i j hij hj).1 hsweep
    exact hexSweep_vertexPos_eq_of_monotone_up a h0 ts i j hij hj hmono hsweep
  · 
    have hdown : hexStripWinding_runningHead h0 ts i = hexStripWinding_runningHead h0 ts j - 6 := by
      omega
    have hmono := (B.monotoneSweep ts hadm j i hji hi).2 hdown
    exact (hexSweep_vertexPos_eq_of_monotone_down a h0 ts j i hji hi hmono hdown).symm

end HexStripSimplyConnectedMonotone
end StatMech.Universality
