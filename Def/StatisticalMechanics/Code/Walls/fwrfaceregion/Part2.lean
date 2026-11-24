module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
public import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
public import Theorem.StatisticalMechanics.Code.Walls.dowdartwinding
public import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
public import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part2
open Set SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def fwr_PrimalWalkBoundsFaceRegion : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup →
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc))


end Walls
end StatMech
