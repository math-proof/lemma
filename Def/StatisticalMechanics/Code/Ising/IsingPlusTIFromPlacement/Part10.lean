module
public import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
public import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
public import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
public import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
public import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
public import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part9
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


noncomputable def iptp_boxEquiv (d n : ℕ) :
    {x : Site d // x ∈ box d n} ≃ {x : Site d // x ∈ boxFinset d n} :=
  Equiv.subtypeEquivProp (by ext x; rw [mem_boxFinset])


end Ising
end StatMech
