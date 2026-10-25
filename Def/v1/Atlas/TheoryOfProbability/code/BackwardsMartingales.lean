/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Instance.v1.Atlas.TheoryOfProbability.code.BackwardsMartingales
open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology


namespace TheoryOfProbability3

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

attribute [coe] DecreasingFiltration.seq

/-- The *tail σ-algebra* of a decreasing filtration `ℱ`, defined as the
intersection `⨅ n, ℱ n`. This is the σ-algebra of events that lie in every
`ℱ n`, i.e. the limit as the filtration shrinks. -/
@[reducible]
def DecreasingFiltration.tailAlgebra (ℱ : DecreasingFiltration Ω m0) :
    MeasurableSpace Ω :=
  ⨅ n, ℱ.seq n

end TheoryOfProbability3
