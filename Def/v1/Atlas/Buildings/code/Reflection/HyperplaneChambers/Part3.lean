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
import Structure.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part2
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HyperplaneArrangement

/-- The union $\bigcup_{η ∈ \mathcal A} η$ of all hyperplanes in the arrangement. -/
def unionSet (arr : HyperplaneArrangement E) : Set E :=
  ⋃ h ∈ arr.hyperplanes, h.carrier

/-- The complement of the arrangement: points lying on no hyperplane. -/
def complement (arr : HyperplaneArrangement E) : Set E :=
  Set.univ \ arr.unionSet

/-- An arrangement is *locally finite* if around every point only finitely many
hyperplanes meet a small open ball. -/
def IsLocallyFinite (arr : HyperplaneArrangement E) : Prop :=
  ∀ x : E, ∃ ε > 0, Set.Finite {h ∈ arr.hyperplanes |
    (Metric.ball x ε ∩ h.carrier).Nonempty}

end HyperplaneArrangement
end
