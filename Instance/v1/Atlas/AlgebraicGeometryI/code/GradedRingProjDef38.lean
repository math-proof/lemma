/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingProjDef38.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.AlgebraicGeometry.Scheme
public import Def.v1.Atlas.AlgebraicGeometryI.code.GradedRingProjDef38

@[expose] public section

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
