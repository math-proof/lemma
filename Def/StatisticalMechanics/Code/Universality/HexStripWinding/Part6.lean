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
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part6


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexStripWinding_singleRight (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStripWinding inReg a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) where
  H := h0 - 1
  w := h0 - 1
  hHL := le_refl _
  hHU := by omega
  window := by
    intro ts hadm k hk
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    
    have hbase : (h0 - 1 : ℤ) = h0 + (-1) := by ring
    rw [hbase]
    refine hexStripWinding_window_of_boundedPrefixSum h0 (-1) [(-1 : ℤ)] ?_ k hk
    intro j hj
    simp only [List.length_singleton] at hj
    interval_cases j <;> simp


end StatMech.Universality
