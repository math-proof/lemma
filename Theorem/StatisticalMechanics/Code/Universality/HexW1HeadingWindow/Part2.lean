/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean -/

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
import Structure.StatisticalMechanics.Code.Universality.HexW1HeadingWindow


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexWindingBound

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexWindingBound inRegion a h0 z)


theorem heading_eq (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    hexInfra_headAccum h0 ts = S.H := by
  have hv := S.sideExit ts hadm
  have hdvd := hexInfra_finalHeading_mod_of_lastVertex a h0 z S.H ts hadm.2.2 hv
  exact hexW1_heading_eq_of_dvd_six_of_bound h0 S.H ts hdvd (S.bound ts hadm)


theorem exits : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep S.H)
        ∧ (S.w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < S.w + 6) := by
  intro ts hadm
  refine ⟨S.sideExit ts hadm, ?_⟩
  exact hexW1_heading_window_of_eq h0 S.H S.w ts (S.heading_eq ts hadm) S.hHL S.hHU


end HexWindingBound
end StatMech.Universality
