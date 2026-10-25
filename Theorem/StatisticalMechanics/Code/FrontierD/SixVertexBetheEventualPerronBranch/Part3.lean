/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalPerronBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexOpenRootSimplex (sixVertexCanonicalPerronBetheRoots hc k) := by
  by_cases h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p
  · rw [sixVertexCanonicalPerronBetheRoots, dif_pos h]
    exact (Classical.choose_spec h).1
  · rw [sixVertexCanonicalPerronBetheRoots, dif_neg h]
    exact sixVertexHalfFilledBetheRoots_mem_open hc k

theorem sixVertexCanonicalPerronBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) (sixVertexCanonicalPerronBetheRoots hc k) := by
  by_cases h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p
  · rw [sixVertexCanonicalPerronBetheRoots, dif_pos h]
    exact (Classical.choose_spec h).2.1
  · rw [sixVertexCanonicalPerronBetheRoots, dif_neg h]
    exact sixVertexHalfFilledBetheRoots_is_solution hc k

theorem eventually_sixVertexCanonicalPerronBetheRoots_witness
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      SixVertexHalfFilledPerronBranchWitness c k
        (sixVertexCanonicalPerronBetheRoots hc k) := by
  filter_upwards [eventually_exists_sixVertexHalfFilledBethePerronBranch hc]
    with k hk
  have h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p := hk
  rw [sixVertexCanonicalPerronBetheRoots, dif_pos h]
  exact Classical.choose_spec h


end
end StatMech.FrontierD
