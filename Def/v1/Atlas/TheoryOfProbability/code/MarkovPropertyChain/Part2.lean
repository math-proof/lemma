/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TheoryOfProbability.code.MarkovChainConstruction.Part2
import Lemma.Measure.Atlas.v1.TheoryOfProbability.code.MarkovChainConstruction
import Instance.v1.Atlas.TheoryOfProbability.code.MarkovPropertyChain
open MeasureTheory ProbabilityTheory

variable {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]


/-- The expectation `E_x Y` of a path functional `Y` under the Markov chain started from
the point `x ∈ S`. It is the integral of `Y` against the path measure with initial
distribution `δ_x`. -/
noncomputable def markovExpectation
    (S : Type*) [MeasurableSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (Y : (ℕ → S) → ℝ) (x : S) : ℝ :=
  ∫ ω, Y ω ∂(MarkovChainPathMeasure S (Measure.dirac x) κ)

