/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc12_ReimerReflectionInjection (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∃ (T R : Finset α → Finset α),
    (∀ S ∈ rc10_boxSupp 𝒜 ℬ, T S ⊆ S ∧ T S ∈ 𝒜 ∧ S \ T S ∈ ℬ ∧
      T S ⊆ R S ∧ Disjoint (R S) (S \ T S)) ∧
    Set.InjOn R (rc10_boxSupp 𝒜 ℬ)

end StatMech.Walls
