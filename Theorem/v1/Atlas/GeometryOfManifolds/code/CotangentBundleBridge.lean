/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CotangentBundleBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.CotangentBundleBridge
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff
open DifferentialFormSpace


namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]

variable [ChartedSpace H M]

/-- Projection of a built cotangent vector returns its basepoint. -/
@[simp] theorem proj_mk (x : M) (ξ : TangentSpace I x →ₗ[ℝ] ℝ) :
    proj I M (mk I M x ξ) = x := rfl

end CotangentBundle
