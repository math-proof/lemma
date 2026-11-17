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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ZariskiCotangentSpace

@[expose] public section

noncomputable section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The Zariski cotangent space is naturally a module over the residue field. -/
instance ZariskiCotangentSpace.instModule :
    Module (ResidueField R) (ZariskiCotangentSpace R) :=
  inferInstance

end
