/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LogNonnegativeSinusoid
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingGeneralSymbol.Part3
open MeasureTheory


namespace StatMech.FrontierA

theorem triangularIsingCornerFactor_affine
    (e1 e2 : Fin 2) (t1 t2 t3 : Real) :
    triangularIsingCornerFactor e1 e2 t1 t2 t3 =
      triangularIsingCornerFactorConst e1 e2 t2 t3 +
        t1 * triangularIsingCornerFactorCoeff e1 e2 t2 t3 := by
  unfold triangularIsingCornerFactor triangularIsingCornerFactorConst
    triangularIsingCornerFactorCoeff
  ring

theorem triangularIsingCornerFactor_const_coeff_not_both_zero
    (e1 e2 : Fin 2) (t2 t3 : Real) :
    triangularIsingCornerFactorConst e1 e2 t2 t3 ≠ 0 ∨
      triangularIsingCornerFactorCoeff e1 e2 t2 t3 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hconst, hcoeff⟩
  fin_cases e1 <;> fin_cases e2
  all_goals simp [triangularIsingCornerFactorConst,
    triangularIsingCornerFactorCoeff, triangularIsingZ2Sign] at hconst hcoeff
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination (1 - t2) * hconst + (-t2 - 1) * hcoeff
    nlinarith [sq_nonneg t2]
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination (t2 + 1) * hconst + (t2 - 1) * hcoeff
    nlinarith [sq_nonneg t2]
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination -(t2 - 1) * hconst + (t2 + 1) * hcoeff
    nlinarith [sq_nonneg t2]
  · have hx : 2 * (t2 ^ 2 + 1) = 0 := by
      linear_combination (t2 + 1) * hconst - (t2 - 1) * hcoeff
    nlinarith [sq_nonneg t2]

end StatMech.FrontierA
