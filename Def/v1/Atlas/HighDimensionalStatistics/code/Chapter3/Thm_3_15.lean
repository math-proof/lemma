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
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory


namespace Chapter3

/-- The squared `L²` norm of a real-valued function `g` over `[0,1]`,
defined as `∫₀¹ g(x)² dx`. -/
noncomputable def L2normSq (g : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, g x ^ 2

/-- The squared empirical norm of `g` evaluated on the uniform grid `{i/n : i = 0, …, n-1}`,
defined as `(1/n) ∑ g(i/n)²`. -/
noncomputable def empiricalNormSq (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, g ((i : ℝ) / (n : ℝ)) ^ 2

end Chapter3
