/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc55nonproduct.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc56_reflImageSet (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (∃ S ∈ rc20_famCylBoxComp n 𝒜 ℬ,
    ∃ K ∈ (univ : Finset (Finset (Fin n))), ∃ L ∈ (univ : Finset (Finset (Fin n))),
      Disjoint K L ∧ rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ ∧
        R = symmDiff S L) = true)


def rc56_Ares : Finset (Finset (Fin 3)) := {∅, {0}, {1}}


def rc56_Bres : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

end StatMech.Walls
