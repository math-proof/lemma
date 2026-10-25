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
import Structure.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyCurves


noncomputable section

namespace CechCohomologyCurves

attribute [instance] CechDataTwoOpen.addCommGroupU1 CechDataTwoOpen.moduleU1
  CechDataTwoOpen.addCommGroupU2 CechDataTwoOpen.moduleU2
  CechDataTwoOpen.addCommGroupU12 CechDataTwoOpen.moduleU12

variable {k : Type*} [Field k]

/-- The Čech differential `(s₁, s₂) ↦ s₁|_{U₁₂} - s₂|_{U₁₂}` on a two-open cover. -/
def cechDifferential (D : CechDataTwoOpen k) :
    (D.sectionsU1 × D.sectionsU2) →ₗ[k] D.sectionsU12 :=
  LinearMap.coprod D.restriction1 (-D.restriction2)

/-- The 0-th Čech cohomology of a two-open cover, computed as the kernel of the Čech
differential. -/
def cechH0 (D : CechDataTwoOpen k) : Submodule k (D.sectionsU1 × D.sectionsU2) :=
  LinearMap.ker (cechDifferential D)

/-- The 1-st Čech cohomology of a two-open cover, computed as the cokernel of the Čech
differential. -/
def cechH1 (D : CechDataTwoOpen k) :=
  D.sectionsU12 ⧸ LinearMap.range (cechDifferential D)

end CechCohomologyCurves
end
