/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.MarkovChain
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Instance.v1.Atlas.TheoryOfProbability.code.MarkovChainConstruction
open MeasureTheory ProbabilityTheory Kernel Set

variable {S : Type*} [MeasurableSpace S]


section CanonicalMeasure

variable (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsProbabilityMeasure μ]

/-- The canonical measure `P_μ` on path space `ℕ → S` of the Markov chain with initial
distribution `μ` and transition kernel `κ`, built via the Ionescu–Tulcea trajectory measure. -/
noncomputable def markovChainMeasure : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ : ℕ => S) μ (markovLiftKernel κ)

end CanonicalMeasure
