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
import Structure.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part3
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
