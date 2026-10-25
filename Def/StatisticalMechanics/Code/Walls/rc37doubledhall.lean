/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc37_admLeft (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧
    ∃ K ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) = true)


def rc37_rightMem (n : ℕ) (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (Rᶜ ∈ ℬ) = true)


end StatMech.Walls
