/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc57_Anat : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {0, 1}, {2}, {0, 2}}


def rc57_Bnat : Finset (Finset (Fin 3)) := {{1}, {2}, {1, 2}}


noncomputable def rc57_natNbhd (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ((rc20_famCylBoxComp n 𝒜 ℬ).biUnion (fun S => rc21_admComp n 𝒜 ℬ S))
    ∪ (rc20_famCylBoxComp n 𝒜 ℬ ∩ rc20_reflInterComp n 𝒜 ℬ)

end StatMech.Walls
