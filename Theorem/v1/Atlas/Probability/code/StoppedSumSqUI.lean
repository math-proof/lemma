/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StoppedSumSqUI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.Probability.WaldSecondEquation
import Lemma.Measure.Atlas.v1.Probability.code.WaldSecondEquation
open MeasureTheory ProbabilityTheory MeasureTheory.Measure Finset ENNReal Filter

/-- Let `X₁, X₂, …` be i.i.d. with `E[X₁] = 0` and `E[X₁²] < ∞`, and let `T` be a
stopping time (relative to the natural filtration) with `E[T] < ∞`. Writing
`Sₖ = X₁ + ⋯ + Xₖ`, the random variable `max_{0 ≤ k ≤ T} Sₖ²` is integrable. This
is used in conjunction with Wald's second equation to control stopped partial-sum
processes. -/
theorem integrable_maximal_stopped_partial_sum_sq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {T : Ω → ℕ}
    (hT : IsStoppingTime (predictableFiltration m X hX_meas) (fun ω => (T ω : WithTop ℕ)))
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    Integrable (fun ω => (Finset.range (T ω + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
      (fun k => (∑ i ∈ Finset.range k, X i ω) ^ 2)) μ := by
  sorry
