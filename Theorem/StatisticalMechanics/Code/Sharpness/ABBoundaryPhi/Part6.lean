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
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part5
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


@[simp] theorem abbSurfaceEquiv_mk_some {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (x : sctBox d n) (hx : some x ∈ S) :
    abbSurfaceEquiv hocc ⟨some x, hx⟩ =
      (⟨x, mem_abbPhysicalSurface_iff.mpr hx⟩ : abbPhysicalSurface d n S) := by
  apply Subtype.ext
  exact Option.some.inj (abbSurfaceValue_spec hocc ⟨some x, hx⟩).symm

@[simp] theorem abbSurfaceEquiv_symm_apply {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (x : abbPhysicalSurface d n S) :
    (abbSurfaceEquiv hocc).symm x =
      (⟨some (x : sctBox d n),
        mem_abbPhysicalSurface_iff.mp x.property⟩ : S) := rfl


end Sharpness
end StatMech
