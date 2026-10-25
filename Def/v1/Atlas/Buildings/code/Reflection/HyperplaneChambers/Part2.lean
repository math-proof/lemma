/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Instance.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineHyperplane

/-- The Euclidean reflection $E ≃ᵃⁱ E$ across the affine hyperplane $η$. -/
def reflectionMap [CompleteSpace E] [FiniteDimensional ℝ E]
    (h : AffineHyperplane E) : E ≃ᵃⁱ[ℝ] E :=
  EuclideanGeometry.reflection h.toAffineSubspace

end AffineHyperplane
end
