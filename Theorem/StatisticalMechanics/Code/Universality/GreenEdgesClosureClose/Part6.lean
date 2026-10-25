/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part5
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gec2_matched_half_of_greenDichotomy (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent (-n) 0 0 (n + 1)))
    (hgreen : gec2_GreenDichotomy n)
    (hsym : rba_selfDualMeasure.real (verticalCrossingEvent (-n) 0 0 (n + 1))
              = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent (-n) 0 0 (n + 1))
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
    rw [rba_dualVerticalCrossing_eq (-n) 0 0 (n + 1) hmeasV, hsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ
      ≤ rba_selfDualMeasure.real (dualVerticalCrossingEvent (-n) 0 0 (n + 1)) :=
    measureReal_mono hgreen
  rw [hselfDual, hcompl] at hmono
  linarith


theorem gec2_greenDichotomy_iff (n : ℤ) :
    gec2_GreenDichotomy n ↔
      ∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 (n + 1) 0 n → mpd_MatchedFrameDualV ω n := by
  unfold gec2_GreenDichotomy mpd_MatchedFrameDualV
  constructor
  · intro h ω hω
    have : ω ∈ (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ := by
      simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact hω
    exact (mem_dualVerticalCrossingEvent).mp (h this)
  · intro h ω hω
    simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
    exact (mem_dualVerticalCrossingEvent).mpr (h ω hω)


theorem gec2_greenDichotomy_false (n : ℤ) (hn : 1 ≤ n) : ¬ gec2_GreenDichotomy n := by
  rw [gec2_greenDichotomy_iff]
  exact gec2_matchedFrameDualV_false n hn

end Universality
end StatMech
