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
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


def pc2_HoleFree (K : Set (Site 2)) : Prop :=
  ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected


def pc2_BoundaryConnGivenHoleFree : Prop :=
  ∀ (K : Finset (Site 2)), IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    ∀ (hfin : (↑K : Set (Site 2)).Finite),
      FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin)


end Lattice
end StatMech
