/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementReduction
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Structure.StatisticalMechanics.Code.FrontierA.IsingGaussianTrivialityReduction
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

theorem scalarMomentCumulantRecurrence_limit
    (moments cumulants : ℕ → ℕ → ℝ)
    (limitMoments : ℕ → ℝ) (variance : ℝ)
    (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
    (hmoments : ∀ order, Tendsto (fun scale => moments scale order)
      atTop (nhds (limitMoments order)))
    (hcumulants : ∀ order, Tendsto (fun scale => cumulants scale order)
      atTop (nhds (scalarGaussianCumulant variance order))) :
    ∀ order,
      limitMoments (order + 1) =
        ∑ k ∈ Finset.range (order + 1),
          (order.choose k : ℝ) * scalarGaussianCumulant variance (k + 1) *
            limitMoments (order - k) := by
  intro order
  have hsum : Tendsto
      (fun scale => ∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * cumulants scale (k + 1) *
          moments scale (order - k)) atTop
      (nhds (∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * scalarGaussianCumulant variance (k + 1) *
          limitMoments (order - k))) := by
    apply tendsto_finsetSum
    intro k hk
    exact (tendsto_const_nhds.mul (hcumulants (k + 1))).mul
      (hmoments (order - k))
  have hleft := hmoments (order + 1)
  have heq : (fun scale => moments scale (order + 1)) =
      fun scale => ∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * cumulants scale (k + 1) *
          moments scale (order - k) := by
    funext scale
    exact hrecurrence.2 scale order
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hsum


theorem scalarWickMoments_of_cumulant_limits
    (moments cumulants : ℕ → ℕ → ℝ)
    (limitMoments : ℕ → ℝ) (variance : ℝ)
    (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
    (hmoments : ∀ order, Tendsto (fun scale => moments scale order)
      atTop (nhds (limitMoments order)))
    (hcumulants : ∀ order, Tendsto (fun scale => cumulants scale order)
      atTop (nhds (scalarGaussianCumulant variance order))) :
    ScalarWickMoments variance limitMoments := by
  have hlimit := scalarMomentCumulantRecurrence_limit moments cumulants
    limitMoments variance hrecurrence hmoments hcumulants
  constructor
  · have hone : Tendsto (fun _scale : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hm0 : Tendsto (fun scale => moments scale 0) atTop (nhds 1) := by
      simpa only [hrecurrence.1] using hone
    exact tendsto_nhds_unique (hmoments 0) hm0
  · have h := hlimit 0
    simpa [scalarGaussianCumulant] using h
  · intro n
    have h := hlimit (n + 1)
    rw [Finset.sum_eq_single 1] at h
    · simpa [scalarGaussianCumulant] using h
    · intro b hb hbne
      have hb2 : b + 1 ≠ 2 := by omega
      simp [scalarGaussianCumulant, hb2]
    · simp


theorem ScalarWickMoments.odd_eq_zero
    {variance : ℝ} {moments : ℕ → ℝ}
    (hwick : ScalarWickMoments variance moments) :
    ∀ n, moments (2 * n + 1) = 0 := by
  intro n
  induction n with
  | zero => simpa using hwick.moment_one
  | succ n ih =>
      have h := hwick.recursion (2 * n + 1)
      rw [ih, mul_zero] at h
      have hindex : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [hindex]
      exact h


theorem ScalarWickMoments.fourth_eq_three_mul_sq
    {variance : ℝ} {moments : ℕ → ℝ}
    (hwick : ScalarWickMoments variance moments) :
    moments 4 = 3 * variance ^ 2 := by
  have htwo := hwick.recursion 0
  have hfour := hwick.recursion 2
  rw [hwick.moment_zero] at htwo
  norm_num at htwo hfour
  rw [htwo] at hfour
  nlinarith

end StatMech.FrontierA
