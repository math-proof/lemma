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
public import Structure.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part3

@[expose] public section

open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HyperplaneArrangement

/-- Two points are *separated by the arrangement* if some hyperplane separates them. -/
def SeparatedBy (arr : HyperplaneArrangement E) (x y : E) : Prop :=
  ∃ h ∈ arr.hyperplanes, h.Separates x y

end HyperplaneArrangement
end
