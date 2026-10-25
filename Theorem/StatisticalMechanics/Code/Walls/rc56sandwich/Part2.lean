/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc55nonproduct.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc56sandwich.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc56_witnessedInterResidue_iff_famCylBoxResidue :
    rc56_WitnessedInterResidue ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc56_wall_iff_witnessedInter]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc56_wall_iff_witnessedInter]; exact h n 𝒜 ℬ

open Classical in


theorem rc56_reimer_closes_of_witnessedInterResidue (h : rc56_WitnessedInterResidue) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (rc56_witnessedInterResidue_iff_famCylBoxResidue.mp h)


end StatMech.Walls
