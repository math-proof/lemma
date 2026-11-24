module
public import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Mathlib.Combinatorics.Hall.Basic
public import Theorem.StatisticalMechanics.Code.Walls.rc49doubled
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc49_neighbourhood (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  (rc10_reflInter 𝒜 ℬ).filter (fun R => ∃ K L : Finset α, Disjoint K L ∧
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) ∧
    rc49_jointImage S K L = R)

end StatMech.Walls
