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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CotangentSpaceDef.Part2


noncomputable section

namespace ZariskiCotangentSpace

open IsLocalRing

variable (k : Type*) [Field k]

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R]

example : Module k (tangentSpace k R) := inferInstance

end ZariskiCotangentSpace
end
