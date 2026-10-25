/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialFormsBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialFormsBridge
open scoped Manifold


namespace MfdDiffForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- Pointwise addition makes `MfdDiffForm k I M` into an additive commutative group. -/
noncomputable instance instAddCommGroup : AddCommGroup (MfdDiffForm k I M) :=
  Pi.addCommGroup

/-- Pointwise scalar multiplication makes `MfdDiffForm k I M` into a real vector space. -/
noncomputable instance instModule : Module ℝ (MfdDiffForm k I M) :=
  Pi.module _ _ _

end MfdDiffForm
