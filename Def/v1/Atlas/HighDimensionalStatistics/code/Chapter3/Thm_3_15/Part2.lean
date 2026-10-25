/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Thm_3_11
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_11
import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory


namespace Chapter3

/-- The trigonometric linear combination `∑_{j=0}^{M-1} θ_j · φ_{j+1}(x)` where
`φ_k` denotes the `k`-th element of the trigonometric basis. -/
noncomputable def trigLinComb (M : ℕ) (θ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin M, θ j * trigBasis (j.val + 1) x

/-- `θhat` is a least-squares estimator for the trigonometric regression: for every
`ω` it minimizes the empirical squared error `∑ (Y_i - φ_θ(i/n))²` over all `θ`. -/
def IsLSEstimator {Ω : Type*} {n M : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin M → ℝ) : Prop :=
  ∀ ω θ,
    ∑ i : Fin n, (Y ω i - trigLinComb M (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 ≤
    ∑ i : Fin n, (Y ω i - trigLinComb M θ ((i : ℝ) / (n : ℝ))) ^ 2

end Chapter3
