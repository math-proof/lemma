/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingFix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- Sobolev embedding (continuity): for `n < 2m`, every element of `SobolevSpace n m` is
represented by a continuous function. -/
theorem sobolevSpace_toFun_continuous {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpace n m) : Continuous u.toFun := by

  obtain ⟨v, hv⟩ := sobolevEmbedding_strong (Nat.zero_le m) (by omega) u
  rw [← hv]
  exact v.toZeroAtInftyContinuousMap.continuous_toFun

/-- Sobolev embedding (decay at infinity): for `n < 2m`, every element of `SobolevSpace n m`
is represented by a function tending to `0` along the cocompact filter. -/
theorem sobolevSpace_toFun_zeroAtInfty {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpace n m) :
    Tendsto u.toFun (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  obtain ⟨v, hv⟩ := sobolevEmbedding_strong (Nat.zero_le m) (by omega) u
  rw [← hv]
  exact v.toZeroAtInftyContinuousMap.zero_at_infty'

/-- Sobolev embedding (higher regularity): for `k ≤ m` and `n < 2(m - k)`, every element of
`SobolevSpace n m` is `C^k` smooth. -/
theorem sobolevSpace_contDiff {n m k : ℕ} (hkm : k ≤ m) (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) : ContDiff ℝ (k : ℕ∞) u.toFun := by
  obtain ⟨v, hv⟩ := sobolevEmbedding_strong hkm hm u
  rw [← hv]
  exact v.contDiff_k


/-- The `j`-th weak derivative of an element of `SobolevSpace n m` (for `j ≤ m`) is itself an
element of `SobolevSpace n (m - j)`, represented pointwise by the iterated Fréchet derivative
of the underlying function. -/
theorem sobolevSpace_iteratedFDeriv_norm_tendsto_zero {n m : ℕ}
    (u : SobolevSpace n m)
    (j : ℕ) (hj : j ≤ m) (hm : n < 2 * (m - j)) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ j u.toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  obtain ⟨v, hv⟩ := sobolevEmbedding_strong hj hm u
  have h := v.iteratedFDeriv_zero_at_infty j le_rfl
  rw [hv] at h
  exact h

end SobolevEmbedding
end
