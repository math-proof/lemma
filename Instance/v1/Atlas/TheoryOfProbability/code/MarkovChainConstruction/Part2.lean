/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.MarkovChain
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Def.v1.Atlas.TheoryOfProbability.code.MarkovChainConstruction.Part2
open MeasureTheory ProbabilityTheory Kernel Set

variable {S : Type*} [MeasurableSpace S]


section CanonicalMeasure

variable (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsProbabilityMeasure μ]

/-- `markovChainMeasure κ μ` is a probability measure on path space. -/
instance markovChainMeasure.isProbabilityMeasure :
    IsProbabilityMeasure (markovChainMeasure κ μ) := by
  unfold markovChainMeasure; infer_instance

end CanonicalMeasure
