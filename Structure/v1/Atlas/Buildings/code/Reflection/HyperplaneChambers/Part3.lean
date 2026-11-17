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
public import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part3
open scoped InnerProductSpace
open Set


public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HyperplaneArrangement

/-- A chamber of an arrangement: a maximal connected subset of the complement of all
hyperplanes. -/
structure Chamber (arr : HyperplaneArrangement E) where
  set : Set E
  subset_complement : set ⊆ arr.complement
  isConnected : IsConnected set
  is_maximal : ∀ S : Set E, S ⊆ arr.complement → IsConnected S → set ⊆ S → S ⊆ set

end HyperplaneArrangement
end
