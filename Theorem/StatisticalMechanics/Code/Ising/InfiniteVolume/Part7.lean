/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Def.StatisticalMechanics.Code.Ising.InfiniteVolume.Part7
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem exists_infiniteVolumeState
    (ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))) :
    ∃ μ : ProbabilityMeasure (ConfigSpace (Site d)), InfiniteVolumeState ρ μ := by
  obtain ⟨ν, φ, hφ, htends⟩ := prokhorov_seq_compact ρ
  exact ⟨ν, φ, hφ, htends⟩


end Ising
end StatMech
