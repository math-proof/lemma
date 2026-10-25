/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.MarkovChain
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Def.v1.Atlas.TheoryOfProbability.code.MarkovChainConstruction
open MeasureTheory ProbabilityTheory Kernel Set

variable {S : Type*} [MeasurableSpace S]


section LiftKernel

/-- The lifted kernel `markovLiftKernel κ n` is again a Markov kernel whenever `κ` is. -/
instance markovLiftKernel.instIsMarkovKernel (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovLiftKernel κ n) := by
  unfold markovLiftKernel; infer_instance

end LiftKernel
