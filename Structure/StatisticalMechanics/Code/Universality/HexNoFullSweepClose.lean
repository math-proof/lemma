/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexNoFullSweepClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


structure HexStripSimplyConnectedMonotone (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  
  w : ℤ
  
  hHL : w ≤ H
  
  hHU : H < w + 6
  
  hh0L : w ≤ h0
  
  hh0U : h0 < w + 6
  
  wall : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k
  
  attainsWall : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∃ p, p ≤ ts.length ∧ hexStripWinding_runningHead h0 ts p = w
  

  monotoneSweep : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ p q, p ≤ q → q ≤ ts.length →
        (hexStripWinding_runningHead h0 ts q = hexStripWinding_runningHead h0 ts p + 6 →
          ∀ k, p ≤ k → k < q → ts[k]?.getD 0 = 1)
        ∧ (hexStripWinding_runningHead h0 ts q = hexStripWinding_runningHead h0 ts p - 6 →
          ∀ k, p ≤ k → k < q → ts[k]?.getD 0 = -1)

end StatMech.Universality
