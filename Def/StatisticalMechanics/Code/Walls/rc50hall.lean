/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc49doubled.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc50hall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc50_InjectiveSelection (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∃ w : Finset α → Finset α × Finset α,
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Disjoint (w S).1 (w S).2 ∧
      (∀ T : Finset α, T ∩ (w S).1 = S ∩ (w S).1 → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ (w S).2 = S ∩ (w S).2 → T ∈ ℬ)) ∧
    Set.InjOn (fun S => rc49_jointImage S (w S).1 (w S).2) (rc20_famCylBox 𝒜 ℬ)

end StatMech.Walls
