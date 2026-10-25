/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
open TopologicalSpace Order Topology


/-- The dimension of a topological space `X` (Definition 11): the length of the longest
chain of irreducible closed subsets, modeled here via the topological Krull dimension. -/
noncomputable abbrev dimension (X : Type*) [TopologicalSpace X] : WithBot ℕ∞ :=
  topologicalKrullDim X

