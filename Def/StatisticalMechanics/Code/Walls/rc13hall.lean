/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc13_adm (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  univ.filter (fun R => ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ ∧ T ⊆ R ∧ Disjoint R (S \ T))

end StatMech.Walls
