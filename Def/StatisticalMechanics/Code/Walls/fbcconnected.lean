/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


def fbc_BoundaryReachable (K : Set (Site 2)) : Prop :=
  ∀ f g : Site 2, f ∈ (faceBoundaryGraph K).support → g ∈ (faceBoundaryGraph K).support →
    (faceBoundaryGraph K).Reachable f g


def fbc_AttachStep : Prop :=
  ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
    IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    fbc_BoundaryReachable (↑K : Set (Site 2)) →
    IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2))


def fbc_HasRemovableCell : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    ∃ c ∈ K, c ≠ origin 2 ∧ IsConnectedCluster (K.erase c) ∧
      pc2_HoleFree (↑(K.erase c) : Set (Site 2))


end Walls
end StatMech
