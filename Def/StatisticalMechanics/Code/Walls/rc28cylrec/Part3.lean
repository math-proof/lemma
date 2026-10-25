/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc28cylrec.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc28_reflEComp (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  E.powerset.filter (fun S => decide (S ∈ 𝒜 ∧ E \ S ∈ ℬ) = true)

end StatMech.Walls
