/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Def.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin)

variable {d : ℕ}


@[simp] theorem edgeStraddles_mk (K : Set (Site d)) (x y : Site d) :
    edgeStraddles K s(x, y) ↔ (x ∈ K ↔ y ∉ K) := Iff.rfl

theorem edgeStraddles_comm (K : Set (Site d)) (x y : Site d) :
    edgeStraddles K s(x, y) ↔ edgeStraddles K s(y, x) := by
  rw [edgeStraddles_mk, edgeStraddles_mk]
  classical
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto


end Lattice
end StatMech
