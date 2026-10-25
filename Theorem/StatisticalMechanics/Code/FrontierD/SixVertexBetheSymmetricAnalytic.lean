/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexEvenSymmetricLift_castAdd
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexEvenSymmetricLift m q (Fin.castAdd m j) = -q j.rev := by
  simp [sixVertexEvenSymmetricLift, sixVertexEvenSymmetricLiftLinearMap]

@[simp] theorem sixVertexEvenSymmetricLift_natAdd
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexEvenSymmetricLift m q (Fin.natAdd m j) = q j := by
  simp [sixVertexEvenSymmetricLift, sixVertexEvenSymmetricLiftLinearMap]

theorem sixVertexEvenSymmetricLift_symmetric
    (m : Nat) (q : Fin m → Real) :
    SixVertexRootSymmetric (sixVertexEvenSymmetricLift m q) := by
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · rw [Fin.rev_castAdd]
    have hadd : j.rev.addNat m = Fin.natAdd m j.rev := by
      apply Fin.ext
      simp [Fin.addNat, Fin.natAdd]
      omega
    rw [hadd, sixVertexEvenSymmetricLift_natAdd,
      sixVertexEvenSymmetricLift_castAdd]
    simp
  · have hrev : (Fin.natAdd m j).rev = Fin.castAdd m j.rev := by
      apply Fin.ext
      simp [Fin.rev, Fin.natAdd, Fin.castAdd]
      omega
    rw [hrev, sixVertexEvenSymmetricLift_castAdd,
      sixVertexEvenSymmetricLift_natAdd]
    simp

theorem sixVertexEvenSymmetricLift_injective (m : Nat) :
    Function.Injective (sixVertexEvenSymmetricLift m) := by
  intro q r h
  funext j
  have := congrFun h (Fin.natAdd m j)
  simpa only [sixVertexEvenSymmetricLift_natAdd] using this


end
end StatMech.FrontierD
