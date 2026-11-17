/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_1_5_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2

@[expose] public section

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
