/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiCotangentSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dual.Defs


noncomputable section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Zariski cotangent space (Def 35, Lec 18): for a local ring `R` with
maximal ideal `m`, it is `m/m²` as a vector space over the residue field. -/
abbrev ZariskiCotangentSpace : Type u := CotangentSpace R

end
