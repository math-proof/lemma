/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Analysis.Complex.Basic
public import Def.v1.Atlas.GeometryOfManifolds.code.BundleDFS.Part2
@[expose] public section

noncomputable section

open scoped Manifold

open Bundle


namespace SmoothSections

/-- The zero section of a vector bundle. -/
instance instZero {M : Type*} {V : M → Type*}
    [∀ x, Zero (V x)] : Zero (SmoothSections V) :=
  Pi.instZero

end SmoothSections
end
