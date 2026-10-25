/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62fixpointfin3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc62_isDown3 (𝒜 : Finset (Finset (Fin 3))) : Bool :=
  decide (∀ S ∈ 𝒜, ∀ i : Fin 3, i ∈ S → S.erase i ∈ 𝒜)


def rc62_isUp3 (ℬ : Finset (Finset (Fin 3))) : Bool :=
  decide (∀ S ∈ ℬ, ∀ i : Fin 3, i ∉ S → insert i S ∈ ℬ)

end StatMech.Walls
