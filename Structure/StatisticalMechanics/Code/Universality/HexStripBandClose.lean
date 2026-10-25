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
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


structure HexStripSimplyConnected (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
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
  


  noFullSweep : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
      ∀ i j, i ≤ ts.length → j ≤ ts.length →
        hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6 →
        hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j

end StatMech.Universality
