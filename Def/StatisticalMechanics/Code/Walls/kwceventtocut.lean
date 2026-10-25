/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising


def PrimalWalkBoundsRegion : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), ∃ S : Set (Site 2),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge S s(u, v))


end Walls
end StatMech
