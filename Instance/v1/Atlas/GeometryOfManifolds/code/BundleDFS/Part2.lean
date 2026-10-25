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
import Def.v1.Atlas.GeometryOfManifolds.code.BundleDFS.Part2


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
