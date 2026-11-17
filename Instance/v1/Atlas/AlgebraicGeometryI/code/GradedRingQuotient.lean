/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Def.v1.Atlas.AlgebraicGeometryI.code.GradedRingQuotient

@[expose] public section

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
