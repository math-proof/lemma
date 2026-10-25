/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelCanonicalRoute_target_mem_codeSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    eta.1 ∈ (rlc_twoChannelCanonicalRoutePlan gamma gamma').codeSet
      (rlc_twoChannelCanonicalRoute eta) := by
  constructor
  · intro e he
    have hsubset := rlc_twoChannelCanonicalRoute_open_subset eta
    exact (rlc_mem_twoChannelOpenEdgeSet_iff eta.1 e).mp (hsubset he)
  · intro e hreserved hpayload
    exfalso
    apply hpayload
    simp only [rlc_twoChannelCanonicalRoutePlan]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hreserved⟩


end
end StatMech.Universality
