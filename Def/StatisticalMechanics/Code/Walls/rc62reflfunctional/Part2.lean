/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc62_isDown (n : ℕ) (𝒜 : Finset (Finset (Fin n))) : Bool :=
  decide (∀ S ∈ 𝒜, ∀ i : Fin n, i ∈ S → S.erase i ∈ 𝒜)


def rc62_isUp (n : ℕ) (ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ S ∈ ℬ, ∀ i : Fin n, i ∉ S → insert i S ∈ ℬ)

end StatMech.Walls
