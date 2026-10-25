/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc43reimer
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc43_GlobalCommonWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Prop :=
  ∃ K : Finset (Fin n),
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ)

end StatMech.Walls
