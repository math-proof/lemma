/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrentRel
    (G : SimpleGraph V) (sites : I -> V) :
    LPReplicaCurrentVertex V -> LPReplicaCurrentVertex V -> Prop
  | .inl (.inl x), .inl (.inl y) => G.Adj x y
  | .inl (.inr x), .inl (.inr y) => G.Adj x y
  | .inl (.inl x), .inl (.inr y) => ∃ i, sites i = x ∧ sites i = y
  | .inl (.inr x), .inl (.inl y) => ∃ i, sites i = x ∧ sites i = y
  | .inl (.inl _), .inr false => True
  | .inr false, .inl (.inl _) => True
  | .inl (.inr _), .inr true => True
  | .inr true, .inl (.inr _) => True
  | _, _ => False


def lpReplicaCurrentGraph
    (G : SimpleGraph V) (sites : I -> V) :
    SimpleGraph (LPReplicaCurrentVertex V) :=
  SimpleGraph.fromRel (lpReplicaCurrentRel G sites)

end
end StatMech.Ising
