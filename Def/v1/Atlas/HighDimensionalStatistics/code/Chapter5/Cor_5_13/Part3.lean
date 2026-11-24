module
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
public import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13
open MeasureTheory InformationTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_13.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace GaussianSequenceModel

/-- The real vector with entry `s` at positions where `ω i = true` and `0` elsewhere. -/
def scaledBoolVec {d : ℕ} (ω : Fin d → Bool) (s : ℝ) : Fin d → ℝ :=
  fun i => if ω i then s else 0

end GaussianSequenceModel
end
