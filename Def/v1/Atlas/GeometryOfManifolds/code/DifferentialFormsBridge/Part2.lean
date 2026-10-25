/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialFormsBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.GeometryOfManifolds.code.DifferentialFormsBridge
open scoped Manifold


namespace MfdDiffForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- Evaluation of a `k`-form `ω` at a point `x : M`, yielding the alternating map `ω_x` on `T_xM`. -/
def evalAt (ω : MfdDiffForm k I M) (x : M) : (TangentSpace I x) [⋀^(Fin k)]→ₗ[ℝ] ℝ :=
  ω x

/-- Exterior derivative `d : Ω^k(M) → Ω^{k+1}(M)` of a manifold differential form. -/
noncomputable def pullbackForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {k : ℕ} (f : M → N) (ω : MfdDiffForm k J N) : MfdDiffForm k I M :=
  fun x => (ω (f x)).compLinearMap ((mfderiv I J f x).toLinearMap)

end MfdDiffForm
