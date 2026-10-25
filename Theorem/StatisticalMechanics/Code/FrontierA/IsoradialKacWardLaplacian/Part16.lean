/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part17


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


omit [Fintype V] [DecidableEq V] in
theorem neg_one_mul_coneQuarterPhase_mul_I
    (exceptional : V -> Bool) (v : V) :
    (-1 : Complex) * coneQuarterPhase exceptional v * Complex.I =
      if exceptional v then -1 else 1 := by
  cases h : exceptional v <;>
    simp [coneQuarterPhase, h, Complex.I_mul_I]

omit [DecidableEq V] in


theorem conePhase_prefactor_eq_exceptionSign
    (exceptional : V -> Bool) :
    (-1 : Complex) ^ Fintype.card V *
        (∏ v : V, coneQuarterPhase exceptional v) *
        Complex.I ^ Fintype.card V =
      (-1 : Complex) ^ coneExceptionCount exceptional := by
  have hneg : (∏ _v : V, (-1 : Complex)) =
      (-1 : Complex) ^ Fintype.card V := by simp
  have hI : (∏ _v : V, Complex.I) =
      Complex.I ^ Fintype.card V := by simp
  rw [← hneg, ← hI,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ v : V, (-1 : Complex) * coneQuarterPhase exceptional v * Complex.I) =
        ∏ v : V, if exceptional v then (-1 : Complex) else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      exact neg_one_mul_coneQuarterPhase_mul_I exceptional v
    _ = (-1 : Complex) ^ coneExceptionCount exceptional := by
      rw [coneExceptionCount, Finset.prod_ite]
      simp


end StatMech.FrontierA
