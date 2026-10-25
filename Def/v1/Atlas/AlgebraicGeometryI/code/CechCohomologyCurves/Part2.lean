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
import Instance.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyCurves


noncomputable section

namespace CechCohomologyCurves

attribute [instance] CechDataTwoOpen.addCommGroupU1 CechDataTwoOpen.moduleU1
  CechDataTwoOpen.addCommGroupU2 CechDataTwoOpen.moduleU2
  CechDataTwoOpen.addCommGroupU12 CechDataTwoOpen.moduleU12

variable {k : Type*} [Field k]

/-- The dimension `h⁰` of the 0-th Čech cohomology. -/
def h0 (D : CechDataTwoOpen k) : ℕ :=
  Module.finrank k (cechH0 D)

/-- The dimension `h¹` of the first Čech cohomology. -/
def h1 (D : CechDataTwoOpen k) : ℕ :=
  Module.finrank k (cechH1 D)

/-- The Euler characteristic `χ = h⁰ - h¹` of a two-open Čech datum. -/
def eulerCharacteristic (D : CechDataTwoOpen k) : ℤ :=
  (h0 D : ℤ) - (h1 D : ℤ)

end CechCohomologyCurves
end
