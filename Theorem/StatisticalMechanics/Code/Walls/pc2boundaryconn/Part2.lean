/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Def.StatisticalMechanics.Code.Walls.pc2boundaryconn
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem pc2_single_dualCircuit_of_residue (h : pc2_BoundaryConnGivenHoleFree)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K)
    (hhf : pc2_HoleFree (↑K : Set (Site 2))) (hfin : (↑K : Set (Site 2)).Finite)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (boundarySupport hfin : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges :=
  exists_single_dualCircuit_of_connected hfin (h K hconn hhf hfin) hf₀


end Lattice
end StatMech
