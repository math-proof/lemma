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
public import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part2
open scoped InnerProductSpace
open Set


@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A hyperplane arrangement on $E$: simply a set of affine hyperplanes. -/
structure HyperplaneArrangement (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  hyperplanes : Set (AffineHyperplane E)

end
