/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The partial sum `S_n = ∑_{i < n} 1_{A_i}` of indicators of the first `n` events,
viewed as a real-valued random variable on `Ω`. -/
def partialSumIndicators (A : ℕ → Set Ω) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) ω

/-- The subsequence `φ(k)` used in the proof of the pairwise-independent strong law: it
chooses the first index `n` such that `E[S_n] ≥ (k+1)²`. Because the spacing grows
quadratically, the Chebyshev tail bounds for `S_{φ(k)}/E[S_{φ(k)}]` are summable. -/
noncomputable def sllnSubseq {A : ℕ → Set Ω}
    (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ)
      Filter.atTop Filter.atTop) : ℕ → ℕ :=
  fun k => Nat.find
    ((hES_top.eventually (Filter.eventually_ge_atTop (((k : ℝ) + 1) ^ 2))).exists)
