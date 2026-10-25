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
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part6


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexJordan_simplyConnected_trivial (a : ℂ) (h0 : ℤ) :
    HexStripSimplyConnected (fun m => m = a) a h0 a where
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
  noFullSweep := by
    intro ts hadm i j _hi _hj heq
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    exfalso
    have hi0 : hexStripWinding_runningHead h0 ([] : List ℤ) i = h0 := by
      unfold hexStripWinding_runningHead; simp
    have hj0 : hexStripWinding_runningHead h0 ([] : List ℤ) j = h0 := by
      unfold hexStripWinding_runningHead; simp
    rw [hi0, hj0] at heq; omega


end StatMech.Universality
