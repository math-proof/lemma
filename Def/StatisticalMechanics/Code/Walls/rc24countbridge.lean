module
public import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
public import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
public import Theorem.StatisticalMechanics.Code.Walls.rc24countbridge
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean -/
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


noncomputable def rc24_complCylBox (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K : Finset α,
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ))

end StatMech.Walls
