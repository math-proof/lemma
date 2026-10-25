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
import Def.StatisticalMechanics.Code.Universality.HexStripWinding.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStripWinding_window_of_headingBound (a : ℂ) (h0 : ℤ) (z : ℂ) (w : ℤ)
    (inRegion : ℂ → Prop)
    (hbd : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        ∀ k, k ≤ ts.length →
          w ≤ hexStripWinding_runningHead h0 ts k
            ∧ hexStripWinding_runningHead h0 ts k < w + 6) :
    ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        ∀ k, k ≤ ts.length →
          w ≤ hexStripWinding_runningHead h0 ts k
            ∧ hexStripWinding_runningHead h0 ts k < w + 6 :=
  hbd


theorem hexStripWinding_no_full_turn {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
    (S : HexStripWinding inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (j k : ℕ) (hj : j ≤ ts.length) (hk : k ≤ ts.length) :
    hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts k + 6 := by
  obtain ⟨hjL, hjU⟩ := S.window ts hadm j hj
  obtain ⟨hkL, hkU⟩ := S.window ts hadm k hk
  omega


theorem hexStripWinding_sidePhaseLock (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (zt zb : ℂ)
    (σ x W r : ℝ)
    (St : HexStripWinding inRegion a h0 zt) (Sb : HexStripWinding inRegion a h0 zb)
    (hsexT : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt zt →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = zt + HexWalk.halfStep St.H)
    (hsexB : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt zb →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = zb + HexWalk.halfStep Sb.H)
    (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = W)
    (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) :=
  hexW1_windingSidePhaseLock inRegion a h0 zt zb σ x W r
    (hexStripWinding_toWindingBound inRegion a h0 zt St hsexT)
    (hexStripWinding_toWindingBound inRegion a h0 zb Sb hsexB)
    hWt hWb hreflt hreflb


end StatMech.Universality
