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
import Def.StatisticalMechanics.Code.Ising.InfiniteVolume.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[simp] lemma glue_mem (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) {x : Site d} (hx : x ∈ box d n) :
    glue η τ x = τ ⟨x, hx⟩ := by
  simp [glue, hx]

@[simp] lemma glue_not_mem (η : ConfigSpace (Site d)) {n : ℕ}
    (τ : {x // x ∈ box d n} → Bool) {x : Site d} (hx : x ∉ box d n) :
    glue η τ x = η x := by
  simp [glue, hx]


end Ising
end StatMech
