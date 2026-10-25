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
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part7
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


noncomputable def gvOvr {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) : {x // x ∈ Sout} → Bool :=
  fun x => if hn : (x : Site d) ∈ Sin then τ ⟨x, hn⟩ else σ x


noncomputable def gvRes {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) : {x // x ∈ Sin} → Bool :=
  fun x => σ ⟨x, hsub x.2⟩

end Ising
end StatMech
