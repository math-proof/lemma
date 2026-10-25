/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

def faceBoundaryGraph (S : Set (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ bdEdge S (sharedPrimalEdge f g)
  symm := by
    constructor
    intro f g ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [← sharedPrimalEdge_comm_of_adj hadj]
  loopless := by
    refine ⟨fun f h => ?_⟩
    exact (hypercubicLattice 2).irrefl h.1

end Lattice
end StatMech
