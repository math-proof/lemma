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
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part6
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


lemma gvMeasure_univ (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    (gvMeasure η S β h) Set.univ = 1 := by
  unfold gvMeasure
  rw [Measure.finsetSum_apply _ _ _]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun τ _ => gvProb_nonneg η S β h τ),
    gvProb_sum_eq_one η S β h, ENNReal.ofReal_one]

end Ising
end StatMech
