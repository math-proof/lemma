/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexUmlauf_band_singleRight (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStripBand inReg a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) where
  H := h0 - 1
  w := h0 - 1
  hHL := le_refl _
  hHU := by omega
  hh0L := by omega
  hh0U := by omega
  wall := by
    intro ts hadm k hk
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    simp only [List.length_singleton] at hk
    interval_cases k <;> simp [hexStripWinding_runningHead]
  noFullTurn := by
    intro ts hadm k hk
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    simp only [List.length_singleton] at hk
    interval_cases k <;> simp only [hexStripWinding_runningHead] <;> simp <;> omega


end StatMech.Universality
