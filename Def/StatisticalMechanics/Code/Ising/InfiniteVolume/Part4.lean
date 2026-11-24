module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
public import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part3
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def fvZ (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : ℝ :=
  ∑ τ : {x // x ∈ box d n} → Bool, fvWeight η n B β h τ

end Ising
end StatMech
