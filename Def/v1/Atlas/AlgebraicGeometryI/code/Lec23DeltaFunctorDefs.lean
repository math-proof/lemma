/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DeltaFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec23DeltaFunctorDefs
open CategoryTheory Category Limits Finset

set_option maxHeartbeats 1600000


noncomputable section

universe v u

namespace Lec23DeltaFunctorDefs

attribute [instance] DeltaFunctorDef43.additive

/-- The truncated Euler characteristic `∑_{i=0}^{d} (-1)^i · dims i`, used to compute
sheaf Euler characteristics from cohomological dimensions. -/
def alternatingSum (d : ℕ) (dims : ℕ → ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1), (-1 : ℤ) ^ i * (dims i : ℤ)

end Lec23DeltaFunctorDefs
end
