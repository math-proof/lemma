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
import Structure.StatisticalMechanics.Code.Universality.HexStripBandClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexStripSimplyConnected

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
  (B : HexStripSimplyConnected inRegion a h0 z)


theorem wallField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    B.w ≤ hexStripWinding_runningHead h0 ts k :=
  B.wall ts hadm k hk


theorem noFullTurnField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    hexStripWinding_runningHead h0 ts k ≠ B.w + 6 := by
  have hsaw : (HexWalk.ofTurns a h0 ts).IsSAW := hadm.1.2
  have hno6 := hexJordan_no_revolution_pair a h0 ts hsaw (B.noFullSweep ts hadm)
  have hspan := hexJordan_span_lt_six a h0 ts hadm.1 hno6
  obtain ⟨p, hp, hpw⟩ := B.attainsWall ts hadm
  exact (hexJordan_window_of_span_attained h0 B.w ts hspan p hp hpw
    (fun k hk => B.wall ts hadm k hk)).2 k hk

include B in


theorem spanField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (i j : ℕ) (hi : i ≤ ts.length) (hj : j ≤ ts.length) :
    |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6 := by
  have hno6 := hexJordan_no_revolution_pair a h0 ts hadm.1.2 (B.noFullSweep ts hadm)
  exact hexJordan_span_lt_six a h0 ts hadm.1 hno6 i j hi hj

end HexStripSimplyConnected
end StatMech.Universality
