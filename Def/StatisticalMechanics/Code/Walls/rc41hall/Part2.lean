/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc41_hasCommonCoveringWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) : Bool :=
  decide (∃ K : Finset (Fin n),
    (∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜) ∧
    (∀ S ∈ 𝒯, rc20_traceClass n Kᶜ S ⊆ ℬ) ∧
    Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n))))

end StatMech.Walls
