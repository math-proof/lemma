/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Walls.jcwcutsetwalk
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Def.StatisticalMechanics.Code.Walls.kwffaceclose
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


theorem kwf_walkEdges_iff_faceCut {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {u v : Site 2} (huv : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ Vc.edges.toFinset ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc) := by
  rw [List.mem_toFinset]
  exact fwr_primalWalkBoundsFaceRegion Vc hnd huv


end Walls
end StatMech
