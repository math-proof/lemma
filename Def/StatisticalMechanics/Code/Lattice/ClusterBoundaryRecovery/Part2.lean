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
import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin)

variable {d : ℕ}


def boundaryEdgeSet (K : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | e ∈ (hypercubicLattice d).edgeSet ∧ edgeStraddles K e}


def latticeMinusBoundary (K : Set (Site d)) : SimpleGraph (Site d) where
  Adj x y := (hypercubicLattice d).Adj x y ∧ ¬ edgeStraddles K s(x, y)
  symm := by
    constructor
    intro x y ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [← edgeStraddles_comm]
  loopless := ⟨fun x h => (hypercubicLattice d).irrefl h.1⟩

end Lattice
end StatMech
