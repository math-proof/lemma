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
import Def.v1.Atlas.AlgebraicGeometryI.code.ChowLemmaHelper
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
