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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part2
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The (Zariski) tangent space scheme `Spec(Sym(T*_x X))` at the closed point. -/
noncomputable def tangentSpaceScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (tangentSpaceRing R))

end Lec20TangentCone
