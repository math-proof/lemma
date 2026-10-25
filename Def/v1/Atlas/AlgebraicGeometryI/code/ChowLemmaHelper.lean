/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowLemmaHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Structure.v1.Atlas.AlgebraicGeometryI.code.ChowLemmaHelper
open AlgebraicGeometry CategoryTheory Limits

universe u


noncomputable section

namespace ChowLemmaHelper

attribute [instance] AffineCoverData.fintype AffineCoverData.isOpenImmersion

/-- The number of charts in an `AffineCoverData`. -/
def AffineCoverData.card {X : Scheme.{u}} (c : AffineCoverData X) : ℕ :=
  Fintype.card c.ι

/-- Convert `AffineCoverData` into a Mathlib `Scheme.OpenCover`, forgetting the ambient
embeddings. -/
def AffineCoverData.toOpenCover {X : Scheme.{u}} (c : AffineCoverData X) : X.OpenCover where
  I₀ := c.ι
  X i := Spec (c.R i)
  f := c.f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x => c.covers x, fun i => c.isOpenImmersion i⟩

end ChowLemmaHelper
end
