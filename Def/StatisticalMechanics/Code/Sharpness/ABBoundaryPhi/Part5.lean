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
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part5
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


noncomputable def abbSurfaceEquiv {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) :
    S ≃ abbPhysicalSurface d n S where
  toFun z := ⟨abbSurfaceValue hocc z, by
    apply mem_abbPhysicalSurface_iff.mpr
    rw [← abbSurfaceValue_spec hocc z]
    exact z.property⟩
  invFun x := ⟨some (x : sctBox d n),
    mem_abbPhysicalSurface_iff.mp x.property⟩
  left_inv z := by
    apply Subtype.ext
    exact (abbSurfaceValue_spec hocc z).symm
  right_inv x := by
    apply Subtype.ext
    exact Option.some.inj (abbSurfaceValue_spec hocc
      ⟨some (x : sctBox d n),
        mem_abbPhysicalSurface_iff.mp x.property⟩).symm

end Sharpness
end StatMech
