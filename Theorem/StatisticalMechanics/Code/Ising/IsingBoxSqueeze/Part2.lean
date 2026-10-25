/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.Ising.IsingBoxSqueeze
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem ibs_boundaryFraction_nonneg (d n : ℕ) : 0 ≤ ibs_boundaryFraction d n := by
  unfold ibs_boundaryFraction; positivity


theorem ibs_boundaryFraction_tendsto_zero (hd : 1 ≤ d) :
    Tendsto (ibs_boundaryFraction d) atTop (𝓝 0) :=
  psv_ratio_card_tendsto_zero d hd


theorem ibs_boundaryFraction_comp_tendsto_zero (hd : 1 ≤ d) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun n => ibs_boundaryFraction d (φ n)) atTop (𝓝 0) :=
  (ibs_boundaryFraction_tendsto_zero hd).comp hφ.tendsto_atTop


theorem ibs_decay_of_boundaryBound (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f : ConfigSpace (Site d) →ᵇ ℝ) {φ : ℕ → ℕ}
    (hd : 1 ≤ d) (hφ : StrictMono φ) (C : ℝ)
    (hbound : ∀ n, |pstc_decayFun (fun n => μ (φ n)) g f n| ≤ C * ibs_boundaryFraction d (φ n)) :
    Tendsto (pstc_decayFun (fun n => μ (φ n)) g f) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun n => abs_nonneg _) hbound
  have := (ibs_boundaryFraction_comp_tendsto_zero hd hφ).const_mul C
  rwa [mul_zero] at this


end Ising
end StatMech
