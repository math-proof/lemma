/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc19doublecover.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc19_doubledReflectionAll_iff_cylBoxReflInter :
    rc19_DoubledReflectionAll ↔ rc18_CylBoxReflInter := by
  constructor
  · intro h n A B
    exact rc19_cylBoxReflInter_of_doubledReflection (h n A B)
  · intro h n A B
    exact rc19_doubledReflection_of_cylBoxReflInter (h n A B)


theorem rc19_reimerWprobCore_of_doubledReflectionAll (h : rc19_DoubledReflectionAll) :
    ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter
    (rc19_doubledReflectionAll_iff_cylBoxReflInter.mp h)

end StatMech.Walls
