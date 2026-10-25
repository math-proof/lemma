/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


theorem card_fkMedialVerticallyWindingComponents_le_total
    (pairing : FKMedialLoopPairing T) :
    (fkMedialVerticallyWindingComponents pairing).card ≤
      fkMedialUnorientedVerticalWindingTotal pairing := by
  classical
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ C ∈ fkMedialVerticallyWindingComponents pairing, 1) ≤
        ∑ C ∈ fkMedialVerticallyWindingComponents pairing,
          (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
      apply Finset.sum_le_sum
      intro C hC
      rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero]
      exact (Finset.mem_filter.mp hC).2
    _ ≤ ∑ C : FKMedialLoop T pairing,
          (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.filter_subset _ _
    _ = fkMedialUnorientedVerticalWindingTotal pairing := rfl


end
end StatMech.FrontierD
