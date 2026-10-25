/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.KrullDimension
set_option maxHeartbeats 400000


noncomputable section

open Set

/-- A topological space has the *proper closed finite* property if every proper closed subset
is finite (characteristic of a one-dimensional space such as an irreducible curve). -/
def ProperClosedFinite (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ s : Set X, IsClosed s → s ≠ Set.univ → s.Finite

end
