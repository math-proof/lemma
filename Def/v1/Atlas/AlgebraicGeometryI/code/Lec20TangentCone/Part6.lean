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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The structure morphism `C_x X → X = Spec R` from the tangent cone to the ambient scheme. -/
noncomputable def tangentConeMap (𝔪 : Ideal R) :
    tangentCone 𝔪 ⟶ AlgebraicGeometry.Spec (.of R) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ringHomToAssocGraded 𝔪))

end Lec20TangentCone
