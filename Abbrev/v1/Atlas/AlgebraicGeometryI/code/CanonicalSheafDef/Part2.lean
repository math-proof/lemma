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
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef


noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The conormal module of an ideal `I ⊆ A`, namely `I / I²`. -/
abbrev conormalModule (A : Type u) [CommRing A] (I : Ideal A) : Type u :=
  I.Cotangent

end CanonicalSheafDef
end
