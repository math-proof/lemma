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
open scoped InnerProductSpace
open Set


noncomputable section

/-- An affine hyperplane $H = \{x ∈ E : ⟨n, x⟩ = c\}$ specified by a nonzero normal
vector $n$ and an offset $c$. -/
structure AffineHyperplane (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normal : E
  offset : ℝ
  normal_ne_zero : normal ≠ 0

end
