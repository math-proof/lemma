/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Def.v1.Atlas.AlgebraicGeometryI.code.GradedRingQuotient
set_option maxHeartbeats 400000

open Polynomial


namespace GradedRingQuotient

universe u

variable {A : Type u} [CommRing A]

/-- The associated graded ring is a commutative ring. -/
noncomputable instance assocGradedRing.commRing (I : Ideal A) :
    CommRing (assocGradedRing I) :=
  Ideal.Quotient.commRing (reesIdealFromBase I)

end GradedRingQuotient
