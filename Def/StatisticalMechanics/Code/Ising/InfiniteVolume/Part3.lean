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
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def fvEnergy (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  - (∑ e ∈ B, bond (glue η τ) e) - h * ∑ x ∈ boxFinset d n, spin (glue η τ) x


noncomputable def fvWeight (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) : ℝ :=
  Real.exp (-β * fvEnergy η n B h τ)

end Ising
end StatMech
