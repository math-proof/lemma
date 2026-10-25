/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_sixVertexCanonicalFixedOddChargePerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexFixedOddChargePerronBranchWitness c s k
        (sixVertexCanonicalFixedOddChargePerronBetheRoots hc s k) := by
  filter_upwards
    [eventually_exists_sixVertexFixedOddChargeBethePerronBranch hc s]
      with k hk
  have h : ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p := hk
  rw [sixVertexCanonicalFixedOddChargePerronBetheRoots, dif_pos h]
  exact Classical.choose_spec h

end
end StatMech.FrontierD
