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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingGeneralSymbol.Part3
open MeasureTheory


namespace StatMech.FrontierA

noncomputable def triangularIsingCornerForbiddenRoot
    (e1 e2 : Fin 2) (t2 t3 : Real) : Real :=
  -triangularIsingCornerFactorConst e1 e2 t2 t3 /
    triangularIsingCornerFactorCoeff e1 e2 t2 t3

end StatMech.FrontierA
