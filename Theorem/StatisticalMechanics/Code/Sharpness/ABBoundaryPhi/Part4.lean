/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Mathlib.Data.Finset.Preimage
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part3
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


@[simp] theorem mem_abbSiteSurface_iff {d n : Nat}
    {S : Finset (Option (sctBox d n))} {x : Site d} :
    x ∈ abbSiteSurface d n S ↔
      ∃ hx : x ∈ box d n, some (⟨x, hx⟩ : sctBox d n) ∈ S := by
  classical
  constructor
  · rw [abbSiteSurface, Finset.mem_image]
    rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_abbPhysicalSurface_iff.mp hy⟩
  · rintro ⟨hx, hS⟩
    rw [abbSiteSurface, Finset.mem_image]
    exact ⟨⟨x, hx⟩, mem_abbPhysicalSurface_iff.mpr hS, rfl⟩


theorem abb_surface_eq_some_of_occurs {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) {z : Option (sctBox d n)} (hz : z ∈ S) :
    ∃ x, z = some x := by
  have hdisj := mpi_surfaceEvent_nonempty_disjoint
    (withGhost (sctBoxGraph d n)) (abbTarget d n) S hocc
  rcases z with _ | x
  · exact False.elim
      (Set.disjoint_left.mp hdisj (by simpa using hz) (none_mem_abbTarget d n))
  · exact ⟨x, rfl⟩


end Sharpness
end StatMech
