/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalDensityPerronBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexOpenRootSimplex
      (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
  let stage := sixVertexPerronGaugeStage hc k
  by_cases hs : 0 < stage
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_pos hs]
    exact (Classical.choose_spec
      (sixVertexPerronGaugeThreshold_spec hc hs k
        (sixVertexPerronGaugeStage_threshold_le hc k))).1.1
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_neg hs]
    exact sixVertexCanonicalPerronBetheRoots_mem_open hc k

theorem sixVertexCanonicalDensityPerronBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
  let stage := sixVertexPerronGaugeStage hc k
  by_cases hs : 0 < stage
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_pos hs]
    exact (Classical.choose_spec
      (sixVertexPerronGaugeThreshold_spec hc hs k
        (sixVertexPerronGaugeStage_threshold_le hc k))).1.2.1
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_neg hs]
    exact sixVertexCanonicalPerronBetheRoots_is_solution hc k

theorem eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      SixVertexHalfFilledPerronGaugeWitness hc k
        ((1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 8)
        (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
  have hstagePos : ∀ᶠ k : Nat in atTop,
      0 < sixVertexPerronGaugeStage hc k :=
    (tendsto_sixVertexPerronGaugeStage hc).eventually (eventually_gt_atTop 0)
  filter_upwards [hstagePos] with k hk
  rw [sixVertexCanonicalDensityPerronBetheRoots, dif_pos hk]
  exact Classical.choose_spec
    (sixVertexPerronGaugeThreshold_spec hc hk k
      (sixVertexPerronGaugeStage_threshold_le hc k))

end
end StatMech.FrontierD
