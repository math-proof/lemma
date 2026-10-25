/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc66singletondet.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc67marriagesplit.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


def rc67_ForcedSelfMatchSDR (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n)))
    (g : Finset (Fin n) → Finset (Fin n)) : Prop :=
  Set.InjOn g (rc67_Toff 𝒜 ℬ T) ∧
    (∀ S ∈ rc67_Toff 𝒜 ℬ T, g S ∈ rc59_nbhd 𝒜 ℬ S) ∧
    (∀ S ∈ rc67_Toff 𝒜 ℬ T, g S ∉ rc67_Tin 𝒜 ℬ T)

end StatMech.Walls
