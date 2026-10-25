/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialFormsBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open scoped Manifold


/-- The type of smooth `k`-forms on a manifold `M`: pointwise alternating multilinear maps
`(T_xM)^k → ℝ` indexed by `x : M`. -/
def MfdDiffForm (k : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  ∀ x : M, (TangentSpace I x) [⋀^(Fin k)]→ₗ[ℝ] ℝ

