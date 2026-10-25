/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Complex.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.BundleDFS


noncomputable section

open scoped Manifold

open Bundle


namespace SmoothSections

/-- Sections form an abelian group under pointwise addition. -/
instance instAddCommGroup {M : Type*} {V : M → Type*}
    [∀ x, AddCommGroup (V x)] : AddCommGroup (SmoothSections V) :=
  Pi.addCommGroup

/-- Sections form a real vector space under pointwise scalar multiplication. -/
instance instModule {M : Type*} {V : M → Type*}
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] :
    Module ℝ (SmoothSections V) :=
  Pi.module _ _ _

end SmoothSections
end
