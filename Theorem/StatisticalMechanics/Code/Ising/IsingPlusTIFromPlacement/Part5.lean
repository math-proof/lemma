/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


lemma gvProb_nonneg (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) : 0 ≤ gvProb η S β h τ :=
  div_nonneg (gvWeight_pos η S β h τ).le (gvZ_pos η S β h).le

lemma gvProb_sum_eq_one (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    ∑ τ : {x // x ∈ S} → Bool, gvProb η S β h τ = 1 := by
  unfold gvProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (gvZ_ne_zero η S β h)]; rfl


end Ising
end StatMech
