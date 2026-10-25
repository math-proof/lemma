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
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part2
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


noncomputable def gvEnergy (η : ConfigSpace (Site d)) (S : Finset (Site d)) (h : ℝ)
    (τ : {x // x ∈ S} → Bool) : ℝ :=
  - (∑ e ∈ gvBondTouch S, bond (gvGlue η S τ) e) - h * ∑ x ∈ S, spin (gvGlue η S τ) x


noncomputable def gvWeight (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    (τ : {x // x ∈ S} → Bool) : ℝ :=
  Real.exp (-β * gvEnergy η S h τ)

end Ising
end StatMech
