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
import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part3
open scoped InnerProductSpace
open Set


noncomputable section

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
