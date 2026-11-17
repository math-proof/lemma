/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahlerMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahlerMathlib

@[expose] public section

set_option autoImplicit false


/-- The "advanced Kähler property": $M$ carries some bidegree decomposition data. A marker
proposition asserting the existence of Hodge data on $M$. -/
def advanced_kahler_property (n : ℕ) (M : CompactKahlerManifold n) : Prop :=
  ∃ (_bd : BidegreeDecomposition n M), True

