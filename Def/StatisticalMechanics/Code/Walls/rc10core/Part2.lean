/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc10_BKRSetFamily : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    IsUpperSet (𝒜 : Set (Finset (Fin n))) → IsUpperSet (ℬ : Set (Finset (Fin n))) →
      #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)

end StatMech.Walls
