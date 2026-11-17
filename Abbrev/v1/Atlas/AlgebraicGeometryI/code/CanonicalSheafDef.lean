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


@[expose] public noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The property of being a standard smooth `R`-algebra of relative dimension `n`. -/
abbrev IsSmoothMorphismOfRelDim (n : ℕ) (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Algebra.IsStandardSmoothOfRelativeDimension n R S


end CanonicalSheafDef
end
