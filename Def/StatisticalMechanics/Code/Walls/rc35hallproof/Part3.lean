/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc34butterfly.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc35hallproof.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc35_OneSidedInjection : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ f : Finset (Fin n) → Finset (Fin n),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA n 𝒜 ℬ S

end StatMech.Walls
