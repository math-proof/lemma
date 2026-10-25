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


noncomputable section

namespace CechCohomologyCurves

/-- Čech data for a sheaf relative to a cover by two open sets `U₁, U₂`: the `k`-vector spaces of
sections on `U₁`, `U₂`, `U₁ ∩ U₂`, together with the two restriction maps. -/
structure CechDataTwoOpen (k : Type*) [Field k] where
  sectionsU1 : Type*
  sectionsU2 : Type*
  sectionsU12 : Type*
  [addCommGroupU1 : AddCommGroup sectionsU1]
  [moduleU1 : Module k sectionsU1]
  [addCommGroupU2 : AddCommGroup sectionsU2]
  [moduleU2 : Module k sectionsU2]
  [addCommGroupU12 : AddCommGroup sectionsU12]
  [moduleU12 : Module k sectionsU12]
  restriction1 : sectionsU1 →ₗ[k] sectionsU12
  restriction2 : sectionsU2 →ₗ[k] sectionsU12

end CechCohomologyCurves
end
