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
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef


@[expose] public noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The conormal module of an ideal `I ⊆ A`, namely `I / I²`. -/
abbrev conormalModule (A : Type u) [CommRing A] (I : Ideal A) : Type u :=
  I.Cotangent

end CanonicalSheafDef
end
