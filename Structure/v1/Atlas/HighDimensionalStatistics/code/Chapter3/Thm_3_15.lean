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
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory


namespace Chapter3

/-- Sub-Gaussian noise vector: the coordinates `ε ω i` of `ε : Ω → Fin n → ℝ` are
componentwise sub-Gaussian with variance proxy `σsq`, integrable, with integrable exponentials,
and satisfying the analogous bound for arbitrary linear combinations. -/
structure IsSubGaussianNoiseVec {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop where
  bound : ∀ i : Fin n, ∀ s : ℝ,
    ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)
  integ : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => ε ω i) μ
  exp_integ : ∀ i : Fin n, ∀ s : ℝ,
    MeasureTheory.Integrable (fun ω => Real.exp (s * ε ω i)) μ
  weighted_sum_bound : ∀ (w : Fin n → ℝ), ∀ s : ℝ,
    ∫ ω, Real.exp (s * ∑ i, w i * ε ω i) ∂μ ≤
      Real.exp (σsq * (∑ i, w i ^ 2) * s ^ 2 / 2)

end Chapter3
