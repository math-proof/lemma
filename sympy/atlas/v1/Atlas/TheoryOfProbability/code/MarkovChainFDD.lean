/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Data.Fin.VecNotation

open MeasureTheory ProbabilityTheory ENNReal Set

/-- The finite-dimensional distribution of a Markov chain with initial distribution `mu`
and transition kernel `kappa`. Concretely, `markovFDD mu kappa n A` computes the iterated
integral

  `∫_{A 0} ∫_{A 1} ⋯ ∫_{A n} 1 dκ(xₙ₋₁) ⋯ dκ(x₀) dμ`,

i.e. the probability that the chain visits the sets `A 0, A 1, …, A n` at consecutive
times. -/
noncomputable def markovFDD {S : Type*} [MeasurableSpace S]
    (mu : Measure S) (kappa : Kernel S S) : (n : Nat) -> (Fin (n + 1) -> Set S) -> ENNReal
  | 0, A => mu (A 0)
  | n + 1, A => ∫⁻ x in A 0, markovFDD (kappa x) kappa n (fun i => A i.succ) ∂mu

set_option maxHeartbeats 800000 in
