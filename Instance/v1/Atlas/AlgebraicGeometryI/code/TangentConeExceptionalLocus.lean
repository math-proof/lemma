/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentConeExceptionalLocus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.DirectSum.Ring
import Def.v1.Atlas.AlgebraicGeometryI.code.TangentConeExceptionalLocus
set_option synthInstance.maxHeartbeats 40000


noncomputable section

open Polynomial

namespace TangentCone

variable (R : Type*) [CommRing R] (I : Ideal R)

/-- Additive group structure on the associated graded piece `I^n / I^{n+1}`. -/
instance AssocGradedPiece.instAddCommGroup (n : ℕ) : AddCommGroup (AssocGradedPiece R I n) :=
  inferInstanceAs (AddCommGroup ((I ^ n : Submodule R R) ⧸ _))

/-- `R`-module structure on the associated graded piece `I^n / I^{n+1}`. -/
instance AssocGradedPiece.instModule (n : ℕ) : Module R (AssocGradedPiece R I n) :=
  inferInstanceAs (Module R ((I ^ n : Submodule R R) ⧸ _))

end TangentCone
end
