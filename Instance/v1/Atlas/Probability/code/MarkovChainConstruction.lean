/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Probability.code.MarkovChain
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Def.Probability.MarkovChainConstruction

@[expose] public section

open MeasureTheory ProbabilityTheory Kernel Set

variable {S : Type*} [MeasurableSpace S]


section LiftKernel

/-- The lifted kernel `markovLiftKernel κ n` is again a Markov kernel whenever `κ` is. -/
instance markovLiftKernel.instIsMarkovKernel (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovLiftKernel κ n) := by
  unfold markovLiftKernel; infer_instance

end LiftKernel
