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
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part6
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


noncomputable def abbSiteSurfaceEquiv (d n : Nat)
    (S : Finset (Option (sctBox d n))) :
    abbPhysicalSurface d n S ≃ abbSiteSurface d n S :=
  Equiv.ofBijective
    (fun x ↦ ⟨((x : sctBox d n) : Site d), by
      rw [abbSiteSurface, Finset.mem_image]
      exact ⟨(x : sctBox d n), x.property, rfl⟩⟩)
    ⟨by
      intro x y hxy
      have hsite : ((x : sctBox d n) : Site d) =
          ((y : sctBox d n) : Site d) :=
        congrArg (fun z : abbSiteSurface d n S ↦ (z : Site d)) hxy
      apply Subtype.ext
      exact Subtype.ext hsite,
    by
      rintro ⟨z, hz⟩
      rw [abbSiteSurface, Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨⟨x, hx⟩, rfl⟩⟩

end Sharpness
end StatMech
