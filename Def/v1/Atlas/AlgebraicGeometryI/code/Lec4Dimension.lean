/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Dimension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
open TopologicalSpace


/-- Lecture 4, Definition 11: the dimension of a Noetherian topological space, defined as the
topological Krull dimension (the supremum of lengths of chains of irreducible closed subsets). -/
noncomputable def noetherianTopologicalDim (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] : WithBot ℕ∞ :=
  topologicalKrullDim X

