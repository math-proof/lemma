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
import Structure.v1.Atlas.TheoryOfProbability.code.BackwardsMartingales
open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology


namespace TheoryOfProbability3

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

attribute [coe] DecreasingFiltration.seq

/-- Allow a `DecreasingFiltration` to be applied as a function `ℕ → MeasurableSpace Ω`
via its underlying sequence `seq`. -/
instance : CoeFun (DecreasingFiltration Ω m0) (fun _ => ℕ → MeasurableSpace Ω) where
  coe := DecreasingFiltration.seq

end TheoryOfProbability3
