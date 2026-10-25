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


noncomputable section

open KaehlerDifferential

namespace CanonicalSheafDef

universe u v


/-- The property of being a standard smooth `R`-algebra of relative dimension `n`. -/
abbrev IsSmoothMorphismOfRelDim (n : ℕ) (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Algebra.IsStandardSmoothOfRelativeDimension n R S


end CanonicalSheafDef
end
