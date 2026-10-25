/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def RlcTwoChannelPIMSDiscardedPayloadPacking.embedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' where
  toFun rho := ⟨packing.packConfig rho, packing.packConfig_success rho⟩
  inj' rho sigma h := by
    have hpack := congrArg Subtype.val h
    exact packing.injective_on_fibre rho sigma
      (packing.target_eq_of_pack_eq hpack) hpack

end
end StatMech.Universality
