/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Ideal.Cotangent
public import Class.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef

@[expose] public section

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
