/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexNoFullSweepClose.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexSweep_toWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripSimplyConnectedMonotone inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep B.H) :
    HexWindingBound inRegion a h0 z :=
  hexJordan_toWindingBound inRegion a h0 z (hexSweep_toSimplyConnected inRegion a h0 z B) hsideExit


noncomputable def hexSweep_simplyConnected_trivial (a : ℂ) (h0 : ℤ) :
    HexStripSimplyConnectedMonotone (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  hh0L := le_refl _
  hh0U := by omega
  wall := by
    intro ts hadm k _hk
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    have : hexStripWinding_runningHead h0 ([] : List ℤ) k = h0 := by
      unfold hexStripWinding_runningHead; simp
    rw [this]
  attainsWall := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    exact ⟨0, by simp, by unfold hexStripWinding_runningHead; simp⟩
  monotoneSweep := by
    intro ts hadm p q _hpq _hq
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    have hp0 : hexStripWinding_runningHead h0 ([] : List ℤ) p = h0 := by
      unfold hexStripWinding_runningHead; simp
    have hq0 : hexStripWinding_runningHead h0 ([] : List ℤ) q = h0 := by
      unfold hexStripWinding_runningHead; simp
    refine ⟨?_, ?_⟩ <;> intro hsweep <;> (rw [hp0, hq0] at hsweep; omega)


end StatMech.Universality
