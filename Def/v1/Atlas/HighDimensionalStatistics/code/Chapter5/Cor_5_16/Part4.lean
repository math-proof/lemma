/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_13
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_15
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13.Part3
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_15
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_16
open Real MeasureTheory InformationTheory


noncomputable section

namespace MinimaxL1Ball

/-- The trivial estimator bundled with its measurability proof. -/
def trivialMeasEstimator (d : ℕ) : MeasEstimator d :=
  ⟨trivialEstimator d, measurable_trivialEstimator d⟩

end MinimaxL1Ball
end
