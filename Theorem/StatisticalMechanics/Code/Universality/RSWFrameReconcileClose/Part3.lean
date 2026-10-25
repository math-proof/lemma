/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFrameReconcileClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.Rot90Reindex
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part2
open Set SimpleGraph MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem rfr_symmetric_box_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :=
  des_hsepSquare_false n hn


theorem rfr_matched_rect_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 (n + 1) 0 n))
    (hmatched : rfr_MatchedPlanarDuality n)
    (hsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 (n + 1) 0 n)
              = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 (n + 1) 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
    rw [rba_dualVerticalCrossing_eq 0 (n + 1) 0 n hmeasV, hsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ
      ≤ rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 (n + 1) 0 n) :=
    measureReal_mono hmatched
  rw [hselfDual, hcompl] at hmono
  linarith


theorem rfr_square_half_of_matched (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 (n + 1) 0 n))
    (hmatched : rfr_MatchedPlanarDuality n)
    (hsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 (n + 1) 0 n)
              = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
  le_trans
    (rfr_matched_rect_half n hmeasH hmeasV hmatched hsym)
    (bxa_horizontalCrossing_real_mono_width hn (by omega))


theorem rfr_face_dualCircuit (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  rdv_face_dualCircuit ω n hn hnoH


theorem rfr_no_frameReconcile :
    ¬ ∃ Φ : Site 2 → Site 2, rdv_FrameReconcile Φ :=
  rdv_no_frameReconcile

end Universality
end StatMech
