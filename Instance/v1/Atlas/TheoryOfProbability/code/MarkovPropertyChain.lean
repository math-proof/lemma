/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TheoryOfProbability.code.MarkovChainConstruction.Part2
import Lemma.Measure.Atlas.v1.TheoryOfProbability.code.MarkovChainConstruction
import Def.v1.Atlas.TheoryOfProbability.code.MarkovPropertyChain
open MeasureTheory ProbabilityTheory

variable {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]


/-- When the initial distribution `μ` is a probability measure, the resulting path measure
is itself a probability measure on `ℕ → S`. -/
noncomputable instance MarkovChainPathMeasure.isProbabilityMeasure
    (S : Type*) [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (κ : Kernel S S) [IsMarkovKernel κ] :
    @IsProbabilityMeasure (ℕ → S) MeasurableSpace.pi (MarkovChainPathMeasure S μ κ) := by
  unfold MarkovChainPathMeasure
  infer_instance

/-- When the initial distribution `μ` is finite, the resulting path measure is itself a
finite measure on `ℕ → S`. -/
noncomputable instance MarkovChainPathMeasure.isFiniteMeasure
    (S : Type*) [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ]
    (κ : Kernel S S) [IsMarkovKernel κ] :
    @IsFiniteMeasure (ℕ → S) MeasurableSpace.pi (MarkovChainPathMeasure S μ κ) := by
  unfold MarkovChainPathMeasure ProbabilityTheory.Kernel.trajMeasure
  infer_instance

