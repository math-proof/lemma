/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexOddSymmetricLift_negative
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricLift m q (sixVertexOddNegativeIndex m j) =
      -q j.rev := by
  simp [sixVertexOddSymmetricLift, sixVertexOddSymmetricLiftLinearMap,
    sixVertexOddNegativeIndex]

@[simp] theorem sixVertexOddSymmetricLift_central
    (m : Nat) (q : Fin m → Real) :
    sixVertexOddSymmetricLift m q (sixVertexOddCentralIndex m) = 0 := by
  simp [sixVertexOddSymmetricLift, sixVertexOddSymmetricLiftLinearMap,
    sixVertexOddCentralIndex]

@[simp] theorem sixVertexOddSymmetricLift_positive
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricLift m q (sixVertexOddPositiveIndex m j) = q j := by
  simp [sixVertexOddSymmetricLift, sixVertexOddSymmetricLiftLinearMap,
    sixVertexOddPositiveIndex]

theorem sixVertexOddNegativeIndex_rev
    (m : Nat) (j : Fin m) :
    (sixVertexOddNegativeIndex m j).rev =
      sixVertexOddPositiveIndex m j.rev := by
  apply Fin.ext
  simp [sixVertexOddNegativeIndex, sixVertexOddPositiveIndex,
    Fin.rev, Fin.castAdd, Fin.natAdd]
  omega

theorem sixVertexOddCentralIndex_rev (m : Nat) :
    (sixVertexOddCentralIndex m).rev = sixVertexOddCentralIndex m := by
  apply Fin.ext
  simp [sixVertexOddCentralIndex, Fin.rev, Fin.castAdd]

theorem sixVertexOddPositiveIndex_rev
    (m : Nat) (j : Fin m) :
    (sixVertexOddPositiveIndex m j).rev =
      sixVertexOddNegativeIndex m j.rev := by
  apply Fin.ext
  simp [sixVertexOddNegativeIndex, sixVertexOddPositiveIndex,
    Fin.rev, Fin.castAdd, Fin.natAdd]
  omega

theorem sixVertexOddSymmetricLift_symmetric
    (m : Nat) (q : Fin m → Real) :
    SixVertexRootSymmetric (sixVertexOddSymmetricLift m q) := by
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · refine Fin.lastCases ?_ ?_ j
    · rw [show Fin.castAdd m (Fin.last m) = sixVertexOddCentralIndex m by rfl,
        sixVertexOddCentralIndex_rev]
      simp
    · intro k
      rw [show Fin.castAdd m k.castSucc = sixVertexOddNegativeIndex m k by rfl,
        sixVertexOddNegativeIndex_rev]
      simp
  · rw [show Fin.natAdd (m + 1) j = sixVertexOddPositiveIndex m j by rfl,
      sixVertexOddPositiveIndex_rev]
    simp

theorem sixVertexOddSymmetricLift_injective (m : Nat) :
    Function.Injective (sixVertexOddSymmetricLift m) := by
  intro q r h
  funext j
  have := congrFun h (sixVertexOddPositiveIndex m j)
  simpa using this

end
end StatMech.FrontierD
