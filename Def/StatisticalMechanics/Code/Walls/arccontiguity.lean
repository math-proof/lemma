/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Theorem.StatisticalMechanics.Code.Walls.arrreroute.Part5
import Theorem.StatisticalMechanics.Code.Walls.cycboundary.Part4
import Theorem.StatisticalMechanics.Code.Walls.arccontiguity
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


section BoundaryArc

variable {K : Finset (Site 2)} {c a₀ : Site 2}


def arc_PatchContiguous (K : Finset (Site 2)) (c a₀ : Site 2) : Prop :=
  a₀ ∈ arr_offPatchSet c ∧
    ∀ f : Site 2, f ∈ arr_offPatchSet c →
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
        ∀ w ∈ p.support, w ∈ arr_offPatchSet c


end BoundaryArc
end Walls
end StatMech
