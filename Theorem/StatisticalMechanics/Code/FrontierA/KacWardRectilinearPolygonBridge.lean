/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonJordanEquivalence
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge


namespace StatMech.FrontierA

open scoped BigOperators

open Finset

open StatMech.Onsager

open StatMech.Onsager.BaseCase


@[simp] theorem kwRectilinearVector_zero : kwRectilinearVector 0 = 1 := by
  norm_num [kwRectilinearVector, stepOf]

@[simp] theorem kwRectilinearVector_one : kwRectilinearVector 1 = Complex.I := by
  norm_num [kwRectilinearVector, stepOf]

@[simp] theorem kwRectilinearVector_two : kwRectilinearVector 2 = -1 := by
  norm_num [kwRectilinearVector, stepOf]

@[simp] theorem kwRectilinearVector_three : kwRectilinearVector 3 = -Complex.I := by
  norm_num [kwRectilinearVector, stepOf]

theorem kwRectilinearVector_ne_zero (d : Fin 4) :
    kwRectilinearVector d ≠ 0 := by
  fin_cases d <;> simp


end StatMech.FrontierA
