module
public import Theorem.StatisticalMechanics.Code.FrontierA.LogNonnegativeSinusoid
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingGeneralSymbol.Part2
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

theorem triangularIsingHighTempSymbol_corner_eq_sq
    (J1 J2 J3 : Real) (e1 e2 : Fin 2) :
    triangularIsingHighTempSymbol J1 J2 J3
        (triangularIsingCornerMomentum e1)
        (triangularIsingCornerMomentum e2) =
      triangularIsingCornerFactor e1 e2
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) ^ 2 := by
  fin_cases e1 <;> fin_cases e2 <;>
    simp [triangularIsingCornerMomentum, triangularIsingCornerFactor,
      triangularIsingZ2Sign, triangularIsingHighTempSymbol,
      Real.cos_add] <;> ring

end StatMech.FrontierA
