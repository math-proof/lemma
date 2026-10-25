/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentConeExceptionalLocus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.DirectSum.Ring
set_option synthInstance.maxHeartbeats 40000


noncomputable section

open Polynomial

namespace TangentCone

variable (R : Type*) [CommRing R] (I : Ideal R)

/-- The `n`-th graded piece `I^n / I^{n+1}` of the associated graded ring of
`R` with respect to the ideal `I`. -/
def AssocGradedPiece (n : ℕ) : Type _ :=
  (I ^ n : Submodule R R) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1) : Submodule R R)

end TangentCone
end
