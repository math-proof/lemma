/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAcyclicElimination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGauge
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Mathlib.Algebra.Ring.GeomSum
import Def.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


theorem kwNilpotentResolvent_mul
    {Internal : Type*} [Fintype Internal] [DecidableEq Internal]
    (internal : Matrix Internal Internal ℂ) (nilpotenceIndex : ℕ)
    (hpow : internal ^ nilpotenceIndex = 0) :
    kwNilpotentResolvent internal nilpotenceIndex * (1 - internal) = 1 := by
  rw [kwNilpotentResolvent, geom_sum_mul_neg, hpow, sub_zero]

theorem kw_mul_nilpotentResolvent
    {Internal : Type*} [Fintype Internal] [DecidableEq Internal]
    (internal : Matrix Internal Internal ℂ) (nilpotenceIndex : ℕ)
    (hpow : internal ^ nilpotenceIndex = 0) :
    (1 - internal) * kwNilpotentResolvent internal nilpotenceIndex = 1 := by
  rw [kwNilpotentResolvent, mul_neg_geom_sum, hpow, sub_zero]


end StatMech.FrontierA
