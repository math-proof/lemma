/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part5
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


@[simp] theorem lpTwoGhost_replicaMixedField_inl
    (hf : V -> Real) (x : V) :
    lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide (.inl x) =
      hf x := rfl

@[simp] theorem lpTwoGhost_replicaMixedField_inr
    (hf : V -> Real) (x : V) :
    lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide (.inr x) =
      -hf x := rfl

theorem lpTwoGhost_replicaMixedField_eq
    (hf : V -> Real) :
    lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide =
      Sum.elim hf (fun x => -hf x) := by
  funext x
  rcases x with x | x <;> rfl


theorem lpReplicaMixedField_nonneg_iff_zero
    (hf : V -> Real) (hhf : forall x, 0 <= hf x) :
    (forall w, 0 <=
      lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide w) <->
      forall x, hf x = 0 := by
  constructor
  · intro hm x
    have hp := hhf x
    have hn := hm (Sum.inr x)
    simp only [lpTwoGhost_replicaMixedField_inr] at hn
    linarith
  · intro hz w
    rcases w with x | x
    · simp [hz x]
    · simp [hz x]

end
end StatMech.Ising
