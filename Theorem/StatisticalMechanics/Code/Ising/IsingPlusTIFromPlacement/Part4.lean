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
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part4
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


lemma gvZ_pos (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    0 < gvZ η S β h := by
  unfold gvZ
  exact Finset.sum_pos (fun τ _ => gvWeight_pos η S β h τ) Finset.univ_nonempty

lemma gvZ_ne_zero (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ) :
    gvZ η S β h ≠ 0 := (gvZ_pos η S β h).ne'


end Ising
end StatMech
