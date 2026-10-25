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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part8
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The coordinate ring of the linear tangent space at the closed point of a local ring,
namely the symmetric algebra on the cotangent space. -/
abbrev tangentSpaceRing :=
  SymmetricAlgebra (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)

end Lec20TangentCone
