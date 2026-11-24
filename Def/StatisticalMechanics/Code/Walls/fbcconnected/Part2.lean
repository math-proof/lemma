module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
public import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
public import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part2
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


def fbc_BoundaryConnResidue : Prop :=
  ∀ (K : Finset (Site 2)), IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    fbc_BoundaryReachable (↑K : Set (Site 2))


end Walls
end StatMech
