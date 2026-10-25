/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahlerMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahlerMathlib
set_option autoImplicit false


/-- The "advanced Kähler property": $M$ carries some bidegree decomposition data. A marker
proposition asserting the existence of Hodge data on $M$. -/
def advanced_kahler_property (n : ℕ) (M : CompactKahlerManifold n) : Prop :=
  ∃ (_bd : BidegreeDecomposition n M), True

