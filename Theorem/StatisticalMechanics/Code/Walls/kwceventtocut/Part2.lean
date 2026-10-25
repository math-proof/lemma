/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Def.StatisticalMechanics.Code.Walls.kwceventtocut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising


theorem kwc_latticeDualWalkHasBdEdgeRegion_of_primal
    (hprimal : PrimalWalkBoundsRegion) :
    LatticeDualWalkHasBdEdgeRegion (hypercubicLattice 2) := by
  intro w W
  obtain ⟨S, hS⟩ := hprimal (W.map rot90Iso.symm.toHom)
  refine ⟨S, ?_⟩
  intro u v huv
  rw [kwc_pullback_eq_mapped_edges W]
  exact hS huv


theorem kwc_dualWalkBoundsRegion_of_primal (hprimal : PrimalWalkBoundsRegion) :
    DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge :=
  dualWalkBoundsRegion_lattice_of_bdEdgeMatch
    (kwc_latticeDualWalkHasBdEdgeRegion_of_primal hprimal)


end Walls
end StatMech
