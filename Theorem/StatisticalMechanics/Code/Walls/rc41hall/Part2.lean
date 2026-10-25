/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Def.StatisticalMechanics.Code.Walls.rc41hall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc41_hallOneSidedA_iff_defectZero : rc33_HallOneSidedA ↔ rc41_DefectZero := Iff.rfl

open Classical in


theorem rc41_reimer_closes_of_defectZero (h : rc41_DefectZero) : rc18_CylBoxReflInter :=
  rc33_reimer_closes_of_hallOneSidedA (rc41_hallOneSidedA_iff_defectZero.mpr h)

open Classical in


theorem rc41_reimer_closes_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc18_CylBoxReflInter :=
  rc40_reimer_closes_of_oneSidedInjection h


end StatMech.Walls
