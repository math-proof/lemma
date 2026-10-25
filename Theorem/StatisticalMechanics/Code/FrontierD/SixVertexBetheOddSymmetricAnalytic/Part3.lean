/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOddSymmetricBetheResidual_eq_zero_iff
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    sixVertexOddSymmetricBetheResidual N m c q = 0 ↔
      SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
        (sixVertexOddSymmetricLift m q) := by
  constructor
  · intro h
    apply (sixVertexBetheResidual_eq_zero_iff c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)).1
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · refine Fin.lastCases ?_ ?_ j
      · have hsymm := sixVertexBetheResidual_symmetric (N := N) (c := c)
          (sixVertexOddSymmetricLift_symmetric m q)
          (sixVertexOddCentralIndex m)
        rw [sixVertexOddCentralIndex_rev] at hsymm
        have hscalar : sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) =
          -sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) := by
          simpa only using hsymm
        change sixVertexBetheResidual c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) = 0
        linarith
      · intro k
        have hsymm := sixVertexBetheResidual_symmetric (N := N) (c := c)
          (sixVertexOddSymmetricLift_symmetric m q)
          (sixVertexOddPositiveIndex m k.rev)
        have hzero : sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q)
            (sixVertexOddPositiveIndex m k.rev) = 0 := by
          simpa [sixVertexOddSymmetricBetheResidual] using congrFun h k.rev
        rw [sixVertexOddPositiveIndex_rev] at hsymm
        have hrel : sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (sixVertexOddNegativeIndex m k) =
          -sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q)
              (sixVertexOddPositiveIndex m k.rev) := by
          simpa only [Fin.rev_rev] using hsymm
        change sixVertexBetheResidual c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) (sixVertexOddNegativeIndex m k) = 0
        rw [hrel, hzero, neg_zero]
    · simpa [sixVertexOddSymmetricBetheResidual,
        sixVertexOddPositiveIndex] using congrFun h j
  · intro h
    funext j
    exact (sixVertexBetheResidual_eq_zero_iff c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)).2 h (sixVertexOddPositiveIndex m j)

end
end StatMech.FrontierD
