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
import Class.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef


noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The canonical module ω_X = ∧^d Ω_X (Def 37, Lec 19): the `d`-th exterior power of the
module of Kähler differentials. -/
def canonicalModule (k : Type u) (A : Type v) [CommRing k] [CommRing A]
    [Algebra k A] (d : ℕ) : Submodule A (ExteriorAlgebra A (Ω[A⁄k])) :=
  ⋀[A]^d (Ω[A⁄k])


end CanonicalSheafDef
end
