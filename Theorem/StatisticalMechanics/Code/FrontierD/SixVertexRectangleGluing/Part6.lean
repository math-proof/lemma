/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part5
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleReflectedGlueBoundaryFiber_injective {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    (ξ : SixVertexToroidalBoundary N M) :
    Function.Injective
      (sixVertexRectangleReflectedGlueBoundaryFiber hN hM ξ) := by
  intro omega eta h
  apply sixVertexRectangleReflectedGlue_injective
  exact congrArg Subtype.val h


theorem sixVertexRectangleBoundaryPartitionSum_eq_fiberSum
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c ξ =
      ∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c := by
  rw [sixVertexRectangleBoundaryPartitionSum]
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun omega : SixVertexRectangleArrows N M =>
      sixVertexRectangleBoundary omega = ξ) (by simp)]
  exact (Finset.sum_filter _ _).symm


theorem sixVertexRectangleBoundaryPartitionSum_pow_four
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c ξ ^ 4 =
      ∑ omega : SixVertexRectangleFourBoundaryCopies ξ,
        omega.1.1.weight c * omega.2.1.1.weight c *
          omega.2.2.1.1.weight c * omega.2.2.2.1.weight c := by
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  rw [show (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) ^ 4 =
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) *
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) *
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) *
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) by ring]
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  apply Fintype.sum_congr
  intro omega₀
  apply Fintype.sum_congr
  intro omega₁
  apply Fintype.sum_congr
  intro omega₂
  apply Fintype.sum_congr
  intro omega₃
  ring


theorem sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ) ^ 4 ≤
      sixVertexRectangleBoundaryPartitionSum (N + N) (M + M) c
        (sixVertexToroidalRectangleBoundary
          (sixVertexDoubledToroidalBoundary ξ)) := by
  rw [sixVertexRectangleBoundaryPartitionSum_pow_four]
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  let glue := sixVertexRectangleReflectedGlueBoundaryFiber hN hM ξ
  calc
    ∑ omega : SixVertexRectangleFourBoundaryCopies
          (sixVertexToroidalRectangleBoundary ξ),
        omega.1.1.weight c * omega.2.1.1.weight c *
          omega.2.2.1.1.weight c * omega.2.2.2.1.weight c =
      ∑ omega : SixVertexRectangleFourBoundaryCopies
          (sixVertexToroidalRectangleBoundary ξ),
        (glue omega).1.weight c := by
          apply Fintype.sum_congr
          intro omega
          exact (sixVertexRectangleReflectedGlue_weight hN hM c omega).symm
    _ = ∑ eta ∈ Finset.univ.image glue, eta.1.weight c := by
      rw [Finset.sum_image
        (sixVertexRectangleReflectedGlueBoundaryFiber_injective
          hN hM ξ).injOn]
    _ ≤ ∑ eta : SixVertexRectangleBoundaryFiber
          (sixVertexToroidalRectangleBoundary
            (sixVertexDoubledToroidalBoundary ξ)), eta.1.weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro eta heta hnot
        exact SixVertexRectangleArrows.weight_nonneg hc eta.1


theorem sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ) ^ 4 ≤
      sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c := by
  refine (sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary
    hN hM hc ξ).trans ?_
  unfold sixVertexRectangleToroidalPartitionSum
  exact Finset.single_le_sum
    (fun eta _ => sixVertexRectangleBoundaryPartitionSum_nonneg
      (N + N) (M + M) hc (sixVertexToroidalRectangleBoundary eta))
    (Finset.mem_univ (sixVertexDoubledToroidalBoundary ξ))


theorem sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubled
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) :
    sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c ^ 4 ≤
      sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c := by
  obtain ⟨ξ, hξ⟩ :=
    sixVertexRectangleMaxToroidalBoundary_exists N M c
  rw [← hξ]
  exact sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal
    hN hM hc ξ

end StatMech.FrontierD
