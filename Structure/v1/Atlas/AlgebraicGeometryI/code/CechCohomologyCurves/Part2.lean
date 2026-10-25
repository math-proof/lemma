/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechCohomologyCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Prod
import Def.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyCurves.Part2


noncomputable section

namespace CechCohomologyCurves

attribute [instance] CechDataTwoOpen.addCommGroupU1 CechDataTwoOpen.moduleU1
  CechDataTwoOpen.addCommGroupU2 CechDataTwoOpen.moduleU2
  CechDataTwoOpen.addCommGroupU12 CechDataTwoOpen.moduleU12

variable {k : Type*} [Field k]

/-- Čech data for a line bundle on a curve, packaged with the degree of the line bundle and the
genus of the curve. -/
structure LineBundleCurveData (k : Type*) [Field k] extends CechDataTwoOpen k where
  deg : ℤ
  genus : ℕ


end CechCohomologyCurves
end
