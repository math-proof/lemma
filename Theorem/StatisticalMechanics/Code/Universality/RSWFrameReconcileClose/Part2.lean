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
import Def.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose
open Set SimpleGraph MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem rfr_square_half_of_dominates (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hdom : rfr_DualCrossingDominates n)
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [rfr_dualV_prob_eq n hmeasV, hsqsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      ≤ rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n) := hdom
  rw [hselfDual, hcompl] at hmono
  linarith


theorem rfr_dominates_of_pointwise (n : ℤ)
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
    rfr_DualCrossingDominates n :=
  measureReal_mono hsep


theorem rfr_dominates_iff_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    rfr_DualCrossingDominates n ↔
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [rfr_dualV_prob_eq n hmeasV, hsqsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  unfold rfr_DualCrossingDominates
  rw [hselfDual, hcompl]
  constructor <;> intro h <;> linarith


end Universality
end StatMech
