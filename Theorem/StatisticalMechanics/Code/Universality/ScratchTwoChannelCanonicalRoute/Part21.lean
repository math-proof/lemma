/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase_embedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    packing.recoverBase (packing.embedding rho) =
      rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho := by
  unfold RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase
  split
  · rename_i h
    have hchosen : packing.embedding h.choose = packing.embedding rho :=
      h.choose_spec
    have hrho : h.choose = rho := packing.embedding.injective hchosen
    rw [hrho]
  · rename_i h
    exact False.elim (h ⟨rho, rfl⟩)


end
end StatMech.Universality
