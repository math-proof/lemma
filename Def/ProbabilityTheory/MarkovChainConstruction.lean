/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.MarkovChain
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
open MeasureTheory ProbabilityTheory Kernel Set

variable {S : Type*} [MeasurableSpace S]


section LiftKernel

/-- Lift the Markov kernel `κ : S → S` to a kernel on tuples `(x_0, …, x_n)` by reading off the
last coordinate `x_n` and applying `κ`. This is the form required by the Ionescu–Tulcea trajectory
construction. -/
noncomputable def markovLiftKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((i : ↥(Finset.Iic n)) → S) S :=
  κ.comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

end LiftKernel
