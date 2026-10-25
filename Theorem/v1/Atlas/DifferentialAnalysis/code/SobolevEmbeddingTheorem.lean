/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean -/

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

/-- Sobolev embedding (continuity, alternate form): for `n < 2m`, every Sobolev space element
in `SobolevSpace n m` admits a continuous representative. -/
theorem sobolevSpace_toFun_continuous' {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpace n m) : Continuous u.toFun := by
  have h := sobolevEmbedding_strong (Nat.zero_le m) (by omega : n < 2 * (m - 0)) u
  rw [← h.property]
  exact h.val.toZeroAtInftyContinuousMap.continuous_toFun

/-- Sobolev embedding (vanishing at infinity, alternate form): for `n < 2m`, elements of
`SobolevSpace n m` vanish at infinity. -/
theorem sobolevSpace_toFun_zeroAtInfty' {n m : ℕ} (hm : n < 2 * m)
    (u : SobolevSpace n m) :
    Tendsto u.toFun (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  have h := sobolevEmbedding_strong (Nat.zero_le m) (by omega : n < 2 * (m - 0)) u
  rw [← h.property]
  exact h.val.toZeroAtInftyContinuousMap.zero_at_infty'

/-- Sobolev embedding (smoothness, alternate form): for `k ≤ m` and `n < 2(m - k)`,
elements of `SobolevSpace n m` are `C^k`. -/
theorem sobolevSpace_contDiff' {n m k : ℕ} (hkm : k ≤ m) (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) : ContDiff ℝ (k : ℕ∞) u.toFun := by
  have h := sobolevEmbedding_strong hkm hm u
  rw [← h.property]
  exact h.val.contDiff_k

/-- Decay of `j`-th order derivatives for Sobolev functions: for `j ≤ m` with `n < 2(m - j)`,
the norm of the `j`-th iterated derivative of any element of `SobolevSpace n m` tends to `0`
at infinity. -/
theorem sobolevSpace_iteratedFDeriv_norm_tendsto_zero' {n m : ℕ}
    (u : SobolevSpace n m) (j : ℕ) (hj : j ≤ m) (hm : n < 2 * (m - j)) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖iteratedFDeriv ℝ j u.toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  exact (sobolevEmbedding_strong hj hm u).val.iteratedFDeriv_zero_at_infty j (le_refl j)

end SobolevEmbedding
end
