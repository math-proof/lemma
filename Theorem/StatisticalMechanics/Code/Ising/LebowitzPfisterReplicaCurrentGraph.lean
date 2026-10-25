/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentReflect_left (x : V) :
    lpReplicaCurrentReflect (.inl (.inl x)) = .inl (.inr x) := rfl

@[simp] theorem lpReplicaCurrentReflect_right (x : V) :
    lpReplicaCurrentReflect (.inl (.inr x)) = .inl (.inl x) := rfl

@[simp] theorem lpReplicaCurrentReflect_ghost (b : Bool) :
    lpReplicaCurrentReflect (.inr b : LPReplicaCurrentVertex V) =
      .inr (!b) := rfl

theorem lpReplicaCurrentReflect_involutive :
    Function.Involutive (lpReplicaCurrentReflect (V := V)) := by
  intro x
  rcases x with (x | b)
  · rcases x with x | x <;> rfl
  · simp


end
end StatMech.Ising
