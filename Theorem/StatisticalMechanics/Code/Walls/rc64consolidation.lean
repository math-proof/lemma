/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc63doubledinjection.Part3
import Def.StatisticalMechanics.Code.Walls.rc64consolidation
set_option linter.style.longLine false


set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc64_reimerLeaf_eq : rc64_ReimerLeaf = rc59_IndepHall := rfl


theorem rc64_reimerLeaf_iff :
    rc64_ReimerLeaf ↔
      ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
          𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  Iff.rfl


end StatMech.Walls
