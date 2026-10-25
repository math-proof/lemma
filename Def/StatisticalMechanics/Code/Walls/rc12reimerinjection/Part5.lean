/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc12_reflInjSearch (𝒜 ℬ : Finset (Finset (Fin 2))) : Bool :=
  let box := rc12_boxSuppComp 𝒜 ℬ
  decide (∃ (T R : Finset (Fin 2) → Finset (Fin 2)),
    (∀ S ∈ box, T S ⊆ S ∧ T S ∈ 𝒜 ∧ S \ T S ∈ ℬ ∧ T S ⊆ R S ∧ Disjoint (R S) (S \ T S)) ∧
    ((box.image R).card = box.card))


def rc12_naiveUnionSearch (𝒜 ℬ : Finset (Finset (Fin 2))) : Bool :=
  let box := rc12_boxSuppComp 𝒜 ℬ
  decide (∃ T : Finset (Fin 2) → Finset (Fin 2),
    (∀ S ∈ box, T S ⊆ S ∧ T S ∈ 𝒜 ∧ S \ T S ∈ ℬ) ∧
    ((box.image (fun S => T S ∪ Sᶜ)).card = box.card))

end StatMech.Walls
