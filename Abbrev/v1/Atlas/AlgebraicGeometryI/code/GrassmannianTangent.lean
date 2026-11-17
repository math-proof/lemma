/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Prod
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrassmannianTangent


@[expose] public noncomputable section

open Module (finrank)

namespace Grassmannian

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- The `n`-th graded piece `I^n / I^{n+1}` of the associated graded of `I`. -/
abbrev associatedGradedComponent (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R) ⧸
    Submodule.comap (I ^ n).subtype ((I ^ (n + 1) : Ideal R).restrictScalars R)

end Grassmannian
end
