/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc43reimer.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc44boxineq
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc44_famCylBoxEComp (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun S =>
    ((E.powerset ×ˢ E.powerset).filter (fun p => Disjoint p.1 p.2 ∧
      (∀ T ∈ E.powerset, T ∩ p.1 = S ∩ p.1 → T ∈ 𝒜) ∧
      (∀ T ∈ E.powerset, T ∩ p.2 = S ∩ p.2 → T ∈ ℬ))).Nonempty)


def rc44_reflInterEComp (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun R => R ∈ 𝒜 ∧ E \ R ∈ ℬ)

end StatMech.Walls
