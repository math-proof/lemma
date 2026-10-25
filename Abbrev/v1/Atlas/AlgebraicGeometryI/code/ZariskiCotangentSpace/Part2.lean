/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiCotangentSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Defs
import Instance.v1.Atlas.AlgebraicGeometryI.code.ZariskiCotangentSpace


noncomputable section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The Zariski tangent space, defined as the residue-field dual of the
Zariski cotangent space; equivalently, derivations `R → k`. -/
abbrev ZariskiTangentSpace : Type u :=
  Module.Dual (ResidueField R) (ZariskiCotangentSpace R)

end
