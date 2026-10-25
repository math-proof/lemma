/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevEmbeddingTheorem
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- Sobolev embedding theorem (Theorem 10.1 of Melrose): under `k ≤ m` and `n < 2(m - k)`,
every element of `SobolevSpace n m` is canonically a `ContDiffZeroAtInftyN n k` test function,
i.e. a `C^k` function with all derivatives of order `≤ k` vanishing at infinity. -/
def sobolevEmbeddingThm {n m k : ℕ} (hkm : k ≤ m)
    (hm : n < 2 * (m - k))
    (u : SobolevSpace n m) : TestFunctions.ContDiffZeroAtInftyN n k where
  toZeroAtInftyContinuousMap :=
    { toFun := u.toFun
      continuous_toFun := sobolevSpace_toFun_continuous' (by omega) u
      zero_at_infty' := sobolevSpace_toFun_zeroAtInfty' (by omega) u }
  contDiff_k := sobolevSpace_contDiff' hkm hm u
  iteratedFDeriv_zero_at_infty j hj :=
    sobolevSpace_iteratedFDeriv_norm_tendsto_zero' u j (le_trans hj hkm)
      (by omega)

end SobolevEmbedding
end
