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
import Def.StatisticalMechanics.Code.Universality.HexStripWinding.Part5


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStripWinding_window_of_boundedPrefixSum (h0 lo : ℤ) (ts : List ℤ)
    (hps : ∀ k, k ≤ ts.length → lo ≤ (ts.take k).sum ∧ (ts.take k).sum < lo + 6) :
    ∀ k, k ≤ ts.length →
      (h0 + lo) ≤ hexStripWinding_runningHead h0 ts k
        ∧ hexStripWinding_runningHead h0 ts k < (h0 + lo) + 6 := by
  intro k hk
  obtain ⟨hL, hU⟩ := hps k hk
  unfold hexStripWinding_runningHead
  omega


end StatMech.Universality
