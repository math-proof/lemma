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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingGeneralSymbol.Part2
open MeasureTheory


namespace StatMech.FrontierA

def triangularIsingCornerFactorConst
    (e1 e2 : Fin 2) (t2 t3 : Real) : Real :=
  let s1 := triangularIsingZ2Sign e1
  let s2 := triangularIsingZ2Sign e2
  1 - s2 * t2 - s1 * s2 * t3 - s1 * t2 * t3

def triangularIsingCornerFactorCoeff
    (e1 e2 : Fin 2) (t2 t3 : Real) : Real :=
  -(triangularIsingZ2Sign e1) -
    triangularIsingZ2Sign e1 * triangularIsingZ2Sign e2 * t2 -
    triangularIsingZ2Sign e2 * t3 + t2 * t3

end StatMech.FrontierA
