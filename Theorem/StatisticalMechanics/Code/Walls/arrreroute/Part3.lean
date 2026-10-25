/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean -/

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
import Def.StatisticalMechanics.Code.Walls.arrreroute.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem arr_reRoute_of_cycleDatum {K : Finset (Site 2)} {c a₀ : Site 2}
    (h : arr_ReRouteFromCycle K c a₀) : arr_ReRoute K c a₀ := h


theorem arr_reRouteClause_of_avoidWalk {K : Finset (Site 2)} {c a₀ f : Site 2}
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀)
    (hp : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    ∃ q : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
      ∀ w ∈ q.support, ¬ ats_faceHasCorner c w :=
  ⟨p, hp⟩


end Walls
end StatMech
