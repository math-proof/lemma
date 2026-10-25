/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentFold_left (x : V) :
    lpReplicaCurrentFold
        (.inl (.inl x) : LPReplicaCurrentVertex V) = Sum.inl x := rfl

@[simp] theorem lpReplicaCurrentFold_right (x : V) :
    lpReplicaCurrentFold
        (.inl (.inr x) : LPReplicaCurrentVertex V) = Sum.inl x := rfl

@[simp] theorem lpReplicaCurrentFold_ghost (b : Bool) :
    lpReplicaCurrentFold (.inr b : LPReplicaCurrentVertex V) =
      Sum.inr () := rfl


@[simp] theorem lpReplicaCurrentFold_reflect
    (x : LPReplicaCurrentVertex V) :
    lpReplicaCurrentFold (lpReplicaCurrentReflect x) =
      lpReplicaCurrentFold x := by
  rcases x with (x | b)
  · rcases x with x | x <;> rfl
  · cases b <;> rfl


end
end StatMech.Ising
