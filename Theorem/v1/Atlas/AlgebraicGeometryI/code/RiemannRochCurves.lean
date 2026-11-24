module
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckGroup
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup.Part3
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
open scoped TensorProduct
open nonZeroDivisors


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace RiemannRochCurves

/-- The Riemann–Roch hom on `(1, 0)` (structure sheaf): `1 - g`. -/
theorem rr_value_structure_sheaf (g : ℤ) : rrHom g (1, 0) = 1 - g := by
  show 0 - 1 * (g - 1) = 1 - g; ring

/-- The Riemann–Roch hom on `(0, 1)` (skyscraper of length 1): `1`. -/
theorem rr_value_skyscraper (g : ℤ) : rrHom g (0, 1) = 1 := by
  show 1 - 0 * (g - 1) = 1; ring

end RiemannRochCurves
end
