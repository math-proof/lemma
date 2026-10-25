/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexFixedEvenChargePerronBranchWitness c s k
        (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k) := by
  filter_upwards [eventually_exists_sixVertexFixedEvenChargeBethePerronBranch
    hc s] with k hk
  have h : ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p := hk
  rw [sixVertexCanonicalFixedEvenChargePerronBetheRoots, dif_pos h]
  exact Classical.choose_spec h


end
end StatMech.FrontierD
