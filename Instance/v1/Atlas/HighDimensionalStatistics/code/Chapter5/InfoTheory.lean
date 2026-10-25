/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/InfoTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L2Space
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part5
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
open MeasureTheory InformationTheory Real


noncomputable section

namespace InfoTheory

/-- Decidability instance for `isMinIdx`, obtained classically. -/
instance isMinIdx.decidable {M : ℕ} (f : Fin M → ℝ) : DecidablePred (isMinIdx f) :=
  fun _ => Classical.dec _

end InfoTheory
end
