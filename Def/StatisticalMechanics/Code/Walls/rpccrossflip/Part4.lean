module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
public import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part3
open Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def rpc_CrossEdgeOddIffOnWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    (Odd (Vc.edges.count (rpc_crossEdge u v)) ↔ s(u, v) ∈ Vc.edges)


end Walls
end StatMech
