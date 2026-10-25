/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part3
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boundarySourceCurrentPairPMF_apply
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources)
    (m n : EdgeCurrent G) :
    boundarySourceCurrentPairPMF G beta J hbeta hJ interior
        internalSources exactSecondSources hfirst hsecond (m, n) =
      boundarySourceCurrentPMF G beta J hbeta hJ
          interior internalSources hfirst m *
        currentPMF G beta J hbeta hJ exactSecondSources hsecond n := by
  rw [boundarySourceCurrentPairPMF, PMF.bind_apply, tsum_eq_single m]
  · rw [PMF.map_apply, tsum_eq_single n]
    · simp
    · intro n' hn'
      simp [Ne.symm hn']
  · intro m' hm'
    simp [PMF.map_apply, Ne.symm hm']


theorem boundarySourceCurrentPairPMF_toMeasure_eq_prod
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources) :
    (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
      internalSources exactSecondSources hfirst hsecond).toMeasure =
      (boundarySourceCurrentPMF G beta J hbeta hJ
        interior internalSources hfirst).toMeasure.prod
      (currentPMF G beta J hbeta hJ exactSecondSources hsecond).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨m, n⟩
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    boundarySourceCurrentPairPMF_apply]
  rw [show ({(m, n)} : Set (EdgeCurrent G × EdgeCurrent G)) =
      ({m} : Set (EdgeCurrent G)) ×ˢ ({n} : Set (EdgeCurrent G)) by
        exact Set.singleton_prod_singleton.symm,
    Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]

end StatMech.FrontierB
