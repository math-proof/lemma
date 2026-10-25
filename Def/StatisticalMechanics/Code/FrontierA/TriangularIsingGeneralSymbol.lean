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
open MeasureTheory


namespace StatMech.FrontierA

noncomputable def triangularIsingInnerA
    (J1 J2 J3 k1 : Real) : Real :=
  Real.cosh (2 * J1) * Real.cosh (2 * J2) * Real.cosh (2 * J3) +
    Real.sinh (2 * J1) * Real.sinh (2 * J2) * Real.sinh (2 * J3) -
    Real.sinh (2 * J1) * Real.cos k1

noncomputable def triangularIsingInnerU
    (J2 J3 k1 : Real) : Real :=
  Real.sinh (2 * J2) + Real.sinh (2 * J3) * Real.cos k1

noncomputable def triangularIsingInnerV
    (J3 k1 : Real) : Real :=
  -Real.sinh (2 * J3) * Real.sin k1

end StatMech.FrontierA
