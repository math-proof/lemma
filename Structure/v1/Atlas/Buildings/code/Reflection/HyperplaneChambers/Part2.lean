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
import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part2
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A hyperplane arrangement on $E$: simply a set of affine hyperplanes. -/
structure HyperplaneArrangement (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  hyperplanes : Set (AffineHyperplane E)

end
