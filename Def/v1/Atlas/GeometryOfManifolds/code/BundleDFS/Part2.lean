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
import Instance.v1.Atlas.GeometryOfManifolds.code.BundleDFS


noncomputable section

open scoped Manifold

open Bundle


namespace SmoothSections

/-- Evaluation of a section $\sigma$ at a point $x \in M$. -/
def eval {M : Type*} {V : M → Type*} (σ : SmoothSections V) (x : M) : V x := σ x

end SmoothSections
end
