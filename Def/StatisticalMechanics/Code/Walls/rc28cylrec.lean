/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc28_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧
    (∀ T : Finset α, T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ⊆ E → T ∩ L = S ∩ L → T ∈ ℬ))

end StatMech.Walls
