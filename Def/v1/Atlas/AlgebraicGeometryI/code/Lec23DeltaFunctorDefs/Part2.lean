/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DeltaFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec23DeltaFunctorDefs.Part2
open CategoryTheory Category Limits Finset

set_option maxHeartbeats 1600000


noncomputable section

universe v u

namespace Lec23DeltaFunctorDefs

attribute [instance] DeltaFunctorDef43.additive

attribute [instance] SheafCohomologyData.field

/-- The Euler characteristic of a sheaf `F`, the alternating sum of its cohomology
dimensions truncated at the cohomological dimension `d`. -/
def SheafCohomologyData.eulerChar (data : SheafCohomologyData) (F : data.CohSheaf) : ℤ :=
  alternatingSum data.d (data.cohomDim F)

end Lec23DeltaFunctorDefs
end
