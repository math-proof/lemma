/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LogNonnegativeSinusoid
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
open MeasureTheory


namespace StatMech.FrontierA

noncomputable def triangularIsingSliceA
    (J1 J2 J3 p : Real) : Real :=
  Real.cosh (2 * J1) * Real.cosh (2 * J2) * Real.cosh (2 * J3) +
    Real.sinh (2 * J1) * Real.sinh (2 * J2) * Real.sinh (2 * J3) -
    Real.sinh (2 * J1) * Real.cos p

noncomputable def triangularIsingSliceU
    (J2 J3 p : Real) : Real :=
  Real.sinh (2 * J2) + Real.sinh (2 * J3) * Real.cos p

noncomputable def triangularIsingSliceV
    (J3 p : Real) : Real :=
  -Real.sinh (2 * J3) * Real.sin p

end StatMech.FrontierA
