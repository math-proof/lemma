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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part5
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- Definition 38: the tangent cone of `Spec R` at a point with maximal ideal `𝔪`,
defined as `Spec(gr_𝔪(R))`. -/
noncomputable abbrev definition_38_tangentCone (𝔪 : Ideal R) : AlgebraicGeometry.Scheme :=
  tangentCone 𝔪

end Lec20TangentCone
