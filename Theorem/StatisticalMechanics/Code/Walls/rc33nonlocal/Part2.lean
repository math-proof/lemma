/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc32reflwitness.Part2
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc33nonlocal.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc33_famCylBoxResidue_of_hallOneSidedA (h : rc33_HallOneSidedA) :
    rc20_FamCylBoxResidue :=
  fun n 𝒜 ℬ => rc33_wall_of_hallOneSidedA n 𝒜 ℬ (h n 𝒜 ℬ)

open Classical in


theorem rc33_perSupportReflection_of_hallOneSidedA (h : rc33_HallOneSidedA) :
    rc20_PerSupportReflection :=
  rc20_perSupportReflection_iff_famCylBoxResidue.mpr (rc33_famCylBoxResidue_of_hallOneSidedA h)

open Classical in


theorem rc33_reimer_closes_of_hallOneSidedA (h : rc33_HallOneSidedA) :
    rc18_CylBoxReflInter :=
  rc20_perSupportReflection_iff_cylBoxReflInter.mp (rc33_perSupportReflection_of_hallOneSidedA h)


end StatMech.Walls
