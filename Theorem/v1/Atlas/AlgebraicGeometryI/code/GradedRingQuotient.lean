/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Instance.v1.Atlas.AlgebraicGeometryI.code.GradedRingQuotient
set_option maxHeartbeats 400000

open Polynomial


namespace GradedRingQuotient

universe u

variable {A : Type u} [CommRing A]

/-- If `a ∈ I^p`, then the monomial `a · t^p` belongs to the Rees algebra of `I`. -/
lemma monomial_mem_reesAlgebra (I : Ideal A) (p : ℕ) (a : A) (ha : a ∈ I ^ p) :
    Polynomial.monomial p a ∈ reesAlgebra I :=
  reesAlgebra.monomial_mem.mpr ha

end GradedRingQuotient
