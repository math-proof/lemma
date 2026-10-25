/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_1_5_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2
open MeasureTheory


noncomputable section

namespace Minimax

/-- Per-observation noise variance `σ² / n` of a Gaussian sequence model. -/
def GaussianSequenceModel.noiseVariance (gsm : GaussianSequenceModel) : ℝ :=
  gsm.σ ^ 2 / gsm.n

/-- An estimator in dimension `d` is just a measurable map `ℝ^d → ℝ^d`
sending observations to a parameter estimate. -/
def Estimator (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

end Minimax
end
