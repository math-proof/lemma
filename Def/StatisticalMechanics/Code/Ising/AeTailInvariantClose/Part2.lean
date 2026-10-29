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
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def AeApproxFarOut (μ : Measure (ConfigSpace (Site d))) (s : Set (ConfigSpace (Site d))) : Prop :=
  ∀ (k : ℕ) (ε : ENNReal), 0 < ε →
    ∃ A : Set (ConfigSpace (Site d)), @MeasurableSet _ (outsideSigma (box d k)) A ∧ μ (s ∆ A) < ε


end Ising
end StatMech
