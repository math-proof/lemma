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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part2
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The ideal of the Rees algebra obtained by extending an ideal `𝔪 ⊆ R` along the
structure map; its quotient defines the associated graded ring. -/
noncomputable def reesIdealFromBase (𝔪 : Ideal R) : Ideal (reesAlgebra 𝔪) :=
  Ideal.map (algebraMap R (reesAlgebra 𝔪)) 𝔪

end Lec20TangentCone
