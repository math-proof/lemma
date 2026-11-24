module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin)

variable {d : ℕ}


def edgeStraddles (K : Set (Site d)) (e : Sym2 (Site d)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y => (x ∈ K ↔ y ∉ K), by
    intro x y
    simp only [eq_iff_iff]
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto⟩ e

end Lattice
end StatMech
