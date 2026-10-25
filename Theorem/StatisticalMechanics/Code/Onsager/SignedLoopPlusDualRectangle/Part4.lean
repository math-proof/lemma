/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part5
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

theorem ons_plusDualContour_subset_plusDualFaceEdgeSet
    (n : Nat) (tau : {x // x ∈ box 2 n} -> Bool) :
    ∀ edge ∈ ons_plusDualContour n tau,
      edge ∈ ons_plusDualFaceEdgeSet n := by
  intro edge hedge
  rw [ons_plusDualContour, Finset.mem_image] at hedge
  obtain ⟨primalEdge, hcut, rfl⟩ := hedge
  apply ons_flankFacesSym_mem_plusDualFaceEdgeSet n
  exact (Finset.mem_filter.mp hcut).1

end
end StatMech.Onsager
