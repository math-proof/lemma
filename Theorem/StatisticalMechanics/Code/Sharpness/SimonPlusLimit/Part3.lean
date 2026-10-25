/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Def.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


theorem simonBoundaryIntegral_tendsto (β : ℝ) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0)
      (plusState d β 0)) (S : Finset (Site d)) (o z : Site d) :
    Tendsto
      (fun n ↦ simonBoundaryIntegral β S o z
        (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (simonBoundaryPlus β S o z)) := by
  unfold simonBoundaryIntegral simonBoundaryPlus
  apply tendsto_finset_sum
  intro e he
  apply Tendsto.const_mul
  exact plusMeasure_pair_tendsto β φ hconv e.2 z


theorem plusCorr_simon_of_eventually_finite
    (β : ℝ) (S : Finset (Site d)) (o z : Site d)
    (hfinite : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ᶠ n in atTop,
        (∫ ω, spin ω o * spin ω z
          ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) ≤
        simonBoundaryIntegral β S o z
          (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) :
    plusCorr d β o z ≤ simonBoundaryPlus β S o z := by
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β 0
  exact le_of_tendsto_of_tendsto
    (plusMeasure_pair_tendsto β φ hconv o z)
    (simonBoundaryIntegral_tendsto β φ hconv S o z)
    (hfinite φ hφ)

end Sharpness
end StatMech
