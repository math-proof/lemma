/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrentCoupling
    (J : Sym2 V -> Real) (hf : V -> Real) (r : Real) :
    Sym2 (LPReplicaCurrentVertex V) -> Real :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | .inl (.inl x), .inl (.inl y) => J s(x, y)
    | .inl (.inr x), .inl (.inr y) => J s(x, y)
    | .inl (.inl _), .inl (.inr _) => r
    | .inl (.inr _), .inl (.inl _) => r
    | .inl (.inl x), .inr false => hf x
    | .inr false, .inl (.inl x) => hf x
    | .inl (.inr x), .inr true => hf x
    | .inr true, .inl (.inr x) => hf x
    | _, _ => 0,
    by
      intro a b
      rcases a with (a | g) <;> rcases b with (b | h)
      · rcases a with a | a <;> rcases b with b | b <;>
          simp only [] <;> rw [Sym2.eq_swap]
      · rcases a with a | a <;> cases h <;> simp
      · cases g <;> rcases b with b | b <;> simp
      · cases g <;> cases h <;> simp⟩

end
end StatMech.Ising
