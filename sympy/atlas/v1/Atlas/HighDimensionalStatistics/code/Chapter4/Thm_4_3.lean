/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1
import Mathlib

open MeasureTheory Matrix Real Finset

noncomputable section

namespace SingularValueThresholding


attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/-- Squared Frobenius norm, defined via the Frobenius norm `‖·‖` on matrices. -/
def frobeniusNormSq {d T : ℕ} (A : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ‖A‖ ^ 2

/-- Recommended SVT threshold:
$\tau = 4\sigma\sqrt{\log 12 \cdot (d \vee T)/n} + 2\sigma\sqrt{2\log(1/\delta)/n}$. -/
noncomputable def svtThreshold (σ : ℝ) (n d T : ℕ) (δ : ℝ) : ℝ :=
  4 * σ * Real.sqrt (Real.log 12 * (max d T : ℝ) / n) +
  2 * σ * Real.sqrt (2 * Real.log (1 / δ) / n)

end SingularValueThresholding

end
