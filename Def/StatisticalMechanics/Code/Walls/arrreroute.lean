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
import Theorem.StatisticalMechanics.Code.Walls.arrreroute
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


def arr_ReRoute (K : Finset (Site 2)) (c a₀ : Site 2) : Prop :=
  ∀ f : Site 2, ¬ ats_faceHasCorner c f →
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
    ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
      ∀ w ∈ p.support, ¬ ats_faceHasCorner c w


def arr_Hook (K : Finset (Site 2)) (c : Site 2) : Prop :=
  ∀ f : Site 2, ats_faceHasCorner c f →
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
    ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧
      g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ∧
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f g


end Walls
end StatMech
