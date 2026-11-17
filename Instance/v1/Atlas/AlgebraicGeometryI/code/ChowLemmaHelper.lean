/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowLemmaHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Def.v1.Atlas.AlgebraicGeometryI.code.ChowLemmaHelper

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u


noncomputable section

namespace ChowLemmaHelper

attribute [instance] AffineCoverData.fintype AffineCoverData.isOpenImmersion

/-- The underlying index type of the associated open cover is finite. -/
instance {X : Scheme.{u}} (c : AffineCoverData X) : Fintype c.toOpenCover.I₀ :=
  c.fintype

end ChowLemmaHelper
end
