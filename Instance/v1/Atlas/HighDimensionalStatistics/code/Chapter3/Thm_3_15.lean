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
import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory


namespace Chapter3

/-- Coerce an `IsSubGaussianNoiseVec` witness to its componentwise MGF bound. -/
instance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {ε : Ω → Fin n → ℝ} {σsq : ℝ} {μ : Measure Ω} :
    CoeFun (IsSubGaussianNoiseVec ε σsq μ)
      (fun _ => ∀ i : Fin n, ∀ s : ℝ,
        ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)) where
  coe := IsSubGaussianNoiseVec.bound

end Chapter3
