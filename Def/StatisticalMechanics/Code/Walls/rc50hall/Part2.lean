/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc49doubled.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc50hall.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc50_InjectiveSelectionAll : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), rc50_InjectiveSelection 𝒜 ℬ

end StatMech.Walls
