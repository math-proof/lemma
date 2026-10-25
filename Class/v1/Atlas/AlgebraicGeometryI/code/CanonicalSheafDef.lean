/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Ideal.Cotangent
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef


noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- An `Algebra k A` is smooth of dimension `d` when its module of Kähler differentials
`Ω[A⁄k]` is free, finite, and has rank `d` over `A`. -/
class IsSmoothOfDimension (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] (d : ℕ) : Prop where
  free : Module.Free A (Ω[A⁄k])
  finite : Module.Finite A (Ω[A⁄k])
  finrank_eq : Module.finrank A (Ω[A⁄k]) = d


end CanonicalSheafDef
end
