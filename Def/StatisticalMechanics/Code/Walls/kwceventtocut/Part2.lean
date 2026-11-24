module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part2
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising


def kwc_PrimalWalkLeftRegionMatch : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))


end Walls
end StatMech
