/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc47reimer
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc47_reimer_closes_of_interCardDominatesAll (h : rc47_InterCardDominatesAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc47_famCylBox_le_reflInter_of_interCard 𝒜 ℬ (h n 𝒜 ℬ))


end StatMech.Walls
