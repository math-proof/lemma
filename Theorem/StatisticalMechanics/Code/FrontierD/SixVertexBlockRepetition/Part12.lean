/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part10
open Finset


namespace StatMech.FrontierD

theorem sixVertexHalfFilledStraightBoundary_balanced (N M : ℕ) :
    (sixVertexHalfFilledStraightBoundary N M).Balanced := by
  exact sixVertexHalfFilledRow_upCount N

theorem sixVertexHalfFilledStraightRectangle_boundary (N M : ℕ) :
    sixVertexRectangleBoundary (sixVertexHalfFilledStraightRectangle N M) =
      sixVertexToroidalRectangleBoundary
        (sixVertexHalfFilledStraightBoundary N M) := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexRectangleBoundary, sixVertexHalfFilledStraightRectangle,
      sixVertexToroidalRectangleBoundary,
      sixVertexHalfFilledStraightBoundary]

theorem sixVertexHalfFilledStraightRectangle_localWeight
    (N M : ℕ) (c : ℝ) (v : Fin N × Fin M) :
    (sixVertexHalfFilledStraightRectangle N M).localWeight c v = 1 := by
  cases h : sixVertexHalfFilledRow N v.1 <;>
    simp [sixVertexHalfFilledStraightRectangle,
      SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount,
      SixVertexRectangleArrows.IsCType, h]

theorem sixVertexHalfFilledStraightRectangle_weight
    (N M : ℕ) (c : ℝ) :
    (sixVertexHalfFilledStraightRectangle N M).weight c = 1 := by
  rw [SixVertexRectangleArrows.weight]
  simp [sixVertexHalfFilledStraightRectangle_localWeight]


theorem sixVertexRectangleBalancedPartitionSum_pos
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 < sixVertexRectangleBalancedPartitionSum N M c := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_fiberSum]
  let ξω : SixVertexRectangleBalancedBoundaryFibers N M :=
    ⟨⟨sixVertexHalfFilledStraightBoundary N M,
      sixVertexHalfFilledStraightBoundary_balanced N M⟩,
      ⟨sixVertexHalfFilledStraightRectangle N M,
        sixVertexHalfFilledStraightRectangle_boundary N M⟩⟩
  have hsingle : ξω.2.1.weight c ≤
      ∑ η : SixVertexRectangleBalancedBoundaryFibers N M,
        η.2.1.weight c :=
    Finset.single_le_sum
      (fun η hη => SixVertexRectangleArrows.weight_nonneg hc η.2.1)
      (Finset.mem_univ ξω)
  change (sixVertexHalfFilledStraightRectangle N M).weight c ≤ _ at hsingle
  rw [sixVertexHalfFilledStraightRectangle_weight] at hsingle
  exact zero_lt_one.trans_le hsingle


theorem sixVertexRectangleBalancedPartitionSum_log_blockRepetition
    {N M n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hn : N < n) (hm : M < m) (hneven : Even n) :
    (((n / N) * (m / M) : ℕ) : ℝ) *
        Real.log (sixVertexRectangleBalancedPartitionSum N M c) ≤
      (((n / N) * (m / M) : ℕ) : ℝ) * (N + M : ℝ) * Real.log 2 +
        Real.log (sixVertexRectangleBalancedPartitionSum n m c) := by
  let Q := (n / N) * (m / M)
  let Z := sixVertexRectangleBalancedPartitionSum N M c
  let Z' := sixVertexRectangleBalancedPartitionSum n m c
  have hZ : 0 < Z := sixVertexRectangleBalancedPartitionSum_pos N M hc
  have hZ' : 0 < Z' := sixVertexRectangleBalancedPartitionSum_pos n m hc
  have hfactor : 0 < ((2 : ℝ) ^ (N + M)) ^ Q := by positivity
  have hfinite := sixVertexRectangleBalancedPartitionSum_blockRepetition
    hc hN hM hNeven hn hm hneven
  have hlog := Real.strictMonoOn_log.monotoneOn
    (pow_pos hZ Q) (mul_pos hfactor hZ') hfinite
  rw [Real.log_pow, Real.log_mul hfactor.ne' hZ'.ne',
    Real.log_pow, Real.log_pow] at hlog
  dsimp [Q, Z, Z'] at hlog ⊢
  norm_num at hlog
  convert hlog using 1 <;> push_cast <;> ring


theorem sixVertexRectangleBalancedDensity_blockRepetition
    {N M n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hn : N < n) (hm : M < m) (hneven : Even n) :
    ((((n / N) * (m / M) : ℕ) : ℝ) *
          (Real.log (sixVertexRectangleBalancedPartitionSum N M c) -
            (N + M : ℝ) * Real.log 2)) /
        ((n : ℝ) * (m : ℝ)) ≤
      Real.log (sixVertexRectangleBalancedPartitionSum n m c) /
        ((n : ℝ) * (m : ℝ)) := by
  have hlog := sixVertexRectangleBalancedPartitionSum_log_blockRepetition
    hc hN hM hNeven hn hm hneven
  have hraw : ((((n / N) * (m / M) : ℕ) : ℝ) *
      (Real.log (sixVertexRectangleBalancedPartitionSum N M c) -
        (N + M : ℝ) * Real.log 2)) ≤
      Real.log (sixVertexRectangleBalancedPartitionSum n m c) := by
    linarith
  exact div_le_div_of_nonneg_right hraw (by positivity)

end StatMech.FrontierD
