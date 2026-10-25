/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc43reimer.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc43_globalCommonWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∃ K : Finset (Fin n),
    (∀ S ∈ rc21_boxComp n 𝒜 ℬ, rc20_traceClass n K S ⊆ 𝒜) ∧
    (∀ S ∈ rc21_boxComp n 𝒜 ℬ, rc20_traceClass n Kᶜ S ⊆ ℬ))

end StatMech.Walls
