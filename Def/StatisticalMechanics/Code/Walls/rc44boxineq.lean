/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc43reimer.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc44_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    Finset (Finset α) :=
  E.powerset.filter (fun S => ∃ K L : Finset α, K ⊆ E ∧ L ⊆ E ∧ Disjoint K L ∧
    (∀ T ⊆ E, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T ⊆ E, T ∩ L = S ∩ L → T ∈ ℬ))

open Classical in


noncomputable def rc44_reflInterE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    Finset (Finset α) :=
  E.powerset.filter (fun R => R ∈ 𝒜 ∧ E \ R ∈ ℬ)


def rc44_slab0 (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter (fun S => a ∉ S)


def rc44_slab1 (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter (fun S => a ∈ S)).image (fun S => S.erase a)

end StatMech.Walls
