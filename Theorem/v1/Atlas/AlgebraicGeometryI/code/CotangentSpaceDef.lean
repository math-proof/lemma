/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentSpaceDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CotangentSpaceDef

public section

noncomputable section

namespace ZariskiCotangentSpace

open IsLocalRing

variable (k : Type*) [Field k]

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra k R]

example : Module (ResidueField R) (cotangentSpace R) := inferInstance

end ZariskiCotangentSpace
end
