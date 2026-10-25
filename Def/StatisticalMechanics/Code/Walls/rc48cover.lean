/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc48cover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc48_CoverAll : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨
    rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜)

end StatMech.Walls
