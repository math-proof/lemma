/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.Scheme
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part3
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The quotient ring homomorphism from the Rees algebra onto the associated graded ring. -/
noncomputable def reesToAssocGraded (𝔪 : Ideal R) :
    (reesAlgebra 𝔪) →+* assocGradedRing 𝔪 :=
  Ideal.Quotient.mk (reesIdealFromBase 𝔪)

end Lec20TangentCone
