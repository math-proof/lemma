module
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L2Space
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part5
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Convex.Jensen
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part2
open MeasureTheory InformationTheory Real


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/InfoTheory.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace InfoTheory

/-- The uniform Boolean measure `μ_Bool` is a probability measure. -/
instance μ_Bool_prob : IsProbabilityMeasure μ_Bool :=
  PMF.toMeasure.isProbabilityMeasure _

end InfoTheory
end
