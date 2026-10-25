/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentSpaceDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Dual.Defs


noncomputable section

namespace ZariskiCotangentSpace

open IsLocalRing

variable (k : Type*) [Field k]

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R]

/-- The Zariski cotangent space at a point, defined as the cotangent space of the local ring `R`
(i.e. `𝔪/𝔪²` viewed as a vector space over the residue field). -/
abbrev cotangentSpace : Type _ := IsLocalRing.CotangentSpace R

end ZariskiCotangentSpace
end
