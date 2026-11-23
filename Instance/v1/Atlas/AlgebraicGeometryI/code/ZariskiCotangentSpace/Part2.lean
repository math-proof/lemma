/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiCotangentSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ZariskiCotangentSpace.Part2
@[expose] public section

noncomputable section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Residue-field module structure on the Zariski tangent space. -/
instance ZariskiTangentSpace.instModule :
    Module (ResidueField R) (ZariskiTangentSpace R) :=
  inferInstance

end
