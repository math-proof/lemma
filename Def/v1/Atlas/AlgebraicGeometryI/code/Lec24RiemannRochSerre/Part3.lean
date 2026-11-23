/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre.Part2

@[expose] public section

set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- The Euler characteristic `χ(E) = h⁰(E) - h¹(E)` of a coherent sheaf on the curve. -/
def chi (E : X.Sheaf) : ℤ := ((X.data E).h0 : ℤ) - ((X.data E).h1 : ℤ)

end SmoothCompleteCurveWithSheaves
end Lec24
end
