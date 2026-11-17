/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.MetricSpace.Basic
open scoped InnerProductSpace
open Set


public noncomputable section

/-- An affine hyperplane $H = \{x ∈ E : ⟨n, x⟩ = c\}$ specified by a nonzero normal
vector $n$ and an offset $c$. -/
structure AffineHyperplane (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normal : E
  offset : ℝ
  normal_ne_zero : normal ≠ 0

end
