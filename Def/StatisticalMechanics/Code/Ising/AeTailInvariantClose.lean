/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TIChoquetClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


@[reducible] noncomputable def aetc_finSig (F : Finset (Site d)) :
    MeasurableSpace (ConfigSpace (Site d)) :=
  ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance


def aetc_Cring (d : ℕ) : Set (Set (ConfigSpace (Site d))) :=
  {A | ∃ F : Finset (Site d), MeasurableSet[aetc_finSig F] A}


end Ising
end StatMech
