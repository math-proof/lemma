/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part21
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def
    RlcTwoChannelPIMSDiscardedPayloadPacking.canonicalFibrePacking
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) :
    RlcTwoChannelCanonicalFibrePacking
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) where
  recoverBase := packing.recoverBase
  pack := packing.embedding
  recoverBase_pack := packing.recoverBase_embedding
  pack_injective_on_fibre := fun rho sigma _hbase hpack =>
    packing.embedding.injective hpack
  pack_mem_codeSet := fun rho => by
    have hcompatible := packing.embedding_compatible rho
    obtain ⟨route, hroute, hcode⟩ := hcompatible
    rw [hroute] at hcode
    exact hcode


def RlcBookFaithfulCanonicalPIMSRouteHall {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma') : Prop :=
  let hcentral :=
    rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
      hinc
  let hclosure := rlc_twoChannelClosureFailureCertificate_of_centralFace
    gamma gamma' hcentral
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
    (rlc_twoChannelCanonicalRouteAvailable
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure))


end
end StatMech.Universality
