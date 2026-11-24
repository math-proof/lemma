module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
public import Theorem.StatisticalMechanics.Code.Ising.Peierls.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean -/
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


noncomputable def peierlsBound (d : ℕ) (β : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ)


noncomputable def peierlsRatio (d : ℕ) (β : ℝ) : ℝ := (2 * d : ℝ) * Real.exp (-(2 * β))

end Ising
end StatMech
