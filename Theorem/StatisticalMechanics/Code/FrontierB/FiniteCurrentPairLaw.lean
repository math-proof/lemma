/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw
open MeasureTheory
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sourceCurrentPairPMF_apply
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B)
    (m n : EdgeCurrent G) :
    sourceCurrentPairPMF G beta J hbeta hJ A B hA hB (m, n) =
      currentPMF G beta J hbeta hJ A hA m *
        currentPMF G beta J hbeta hJ B hB n := by
  rw [sourceCurrentPairPMF, PMF.bind_apply, tsum_eq_single m]
  · rw [PMF.map_apply, tsum_eq_single n]
    · simp
    · intro n' hn'
      simp [Ne.symm hn']
  · intro m' hm'
    simp [PMF.map_apply, Ne.symm hm']


theorem sourceCurrentPairPMF_toMeasure_eq_prod
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B) :
    (sourceCurrentPairPMF G beta J hbeta hJ A B hA hB).toMeasure =
      (currentPMF G beta J hbeta hJ A hA).toMeasure.prod
        (currentPMF G beta J hbeta hJ B hB).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨m, n⟩
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    sourceCurrentPairPMF_apply]
  rw [show ({(m, n)} : Set (EdgeCurrent G × EdgeCurrent G)) =
      ({m} : Set (EdgeCurrent G)) ×ˢ ({n} : Set (EdgeCurrent G)) by
        exact Set.singleton_prod_singleton.symm,
    Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]


end StatMech.FrontierB
