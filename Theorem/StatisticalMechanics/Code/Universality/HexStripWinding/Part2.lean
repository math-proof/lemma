/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4
import Structure.StatisticalMechanics.Code.Universality.HexStripWinding


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexStripWinding

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexStripWinding inRegion a h0 z)


theorem headAccum_window (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    S.w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < S.w + 6 := by
  have h := S.window ts hadm ts.length (le_refl _)
  rwa [hexStripWinding_runningHead_length] at h


theorem bound (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - S.H| < 6 := by
  obtain ⟨hgL, hgU⟩ := S.headAccum_window ts hadm
  have hHL := S.hHL
  have hHU := S.hHU
  rw [abs_lt]; omega


theorem heading_eq (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hsideExit : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
        = z + HexWalk.halfStep S.H) :
    hexInfra_headAccum h0 ts = S.H := by
  have hdvd := hexInfra_finalHeading_mod_of_lastVertex a h0 z S.H ts hadm.2.2 hsideExit
  exact hexW1_heading_eq_of_dvd_six_of_bound h0 S.H ts hdvd (S.bound ts hadm)

end HexStripWinding
end StatMech.Universality
