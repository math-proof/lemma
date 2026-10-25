/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingProjDef38.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Scheme
import Def.v1.Atlas.AlgebraicGeometryI.code.GradedRingProjDef38
set_option maxHeartbeats 400000


noncomputable section

open Polynomial AlgebraicGeometry

variable {R : Type*} [CommRing R]

namespace Definition38

/-- The associated graded ring is a commutative ring. -/
noncomputable instance assocGradedRing.instCommRing (𝔪 : Ideal R) :
    CommRing (assocGradedRing 𝔪) :=
  Ideal.Quotient.commRing (reesIdealFromBase 𝔪)

end Definition38
end
