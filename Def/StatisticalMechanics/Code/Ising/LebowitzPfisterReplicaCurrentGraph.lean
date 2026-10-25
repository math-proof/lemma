/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrentReflect : Equiv.Perm (LPReplicaCurrentVertex V) where
  toFun
    | .inl (.inl x) => .inl (.inr x)
    | .inl (.inr x) => .inl (.inl x)
    | .inr b => .inr (!b)
  invFun
    | .inl (.inl x) => .inl (.inr x)
    | .inl (.inr x) => .inl (.inl x)
    | .inr b => .inr (!b)
  left_inv := by
    intro x
    rcases x with (x | b)
    · rcases x with x | x <;> rfl
    · simp
  right_inv := by
    intro x
    rcases x with (x | b)
    · rcases x with x | x <;> rfl
    · simp

end
end StatMech.Ising
