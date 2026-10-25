/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc52pairimage
import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc53butterfly
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc53_boxWithWitness_eq_famCylBoxDoubled (𝒜 ℬ : Finset (Finset α)) :
    rc53_boxWithWitness 𝒜 ℬ = rc46_famCylBoxDoubled 𝒜 ℬ := rfl

open Classical in


theorem rc53_boxWithWitness_card (𝒜 ℬ : Finset (Finset α)) :
    (rc53_boxWithWitness 𝒜 ℬ).card = (rc20_famCylBox 𝒜 ℬ).card :=
  rc46_famCylBoxDoubled_card_eq 𝒜 ℬ


end StatMech.Walls
