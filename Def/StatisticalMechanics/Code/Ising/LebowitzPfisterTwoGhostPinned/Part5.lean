/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part4
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


def lpReplicaSide : V ⊕ V -> Bool
  | .inl _ => false
  | .inr _ => true

def lpReplicaFieldMagnitude (hf : V -> Real) : V ⊕ V -> Real :=
  Sum.elim hf hf

end
end StatMech.Ising
