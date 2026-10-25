/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Structure.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def
    rlc_twoChannelCanonicalForcedFullPIMSDiscardedPayloadPacking {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfixed : RlcTwoChannelPIMSFixedRouteSourceDetermined hclosure) :
    RlcTwoChannelPIMSDiscardedPayloadPacking hclosure where
  packConfig := rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure
  variable_eq :=
    rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq hclosure
  reserved_open :=
    rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open hclosure
  injective_on_fibre := by
    intro rho sigma htarget hpack
    apply Subtype.ext
    apply rlc_twoChannelFullPIMSConfig_injective
    funext e
    by_cases hroute : e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute
          (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1
    · by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let vtarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        calc
          rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 e =
              (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e := by
            exact rlc_twoChannelFullPIMSConfig_variable_eq_projection
              rho.1 vtarget
          _ = (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma).1 e := by
            rw [htarget]
          _ = rlc_twoChannelFullPIMSConfig gamma gamma' sigma.1 e := by
            exact (rlc_twoChannelFullPIMSConfig_variable_eq_projection
              sigma.1 vtarget).symm
      · let ftarget : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        exact congrArg Bool.not (hfixed rho sigma htarget ftarget hroute)
    · have hroute' : e ∉ rlc_twoChannelOpenEdgeSet
          (rlc_twoChannelCanonicalRoute
            (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma)).1 := by
        rwa [← htarget]
      have happ := congrFun hpack e
      simpa only [rlc_twoChannelCanonicalForcedFullPIMSConfig,
        if_neg hroute, if_neg hroute'] using happ


noncomputable def rlc_twoChannelPIMSDiscardedPayloadPackingOfCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure) :
    RlcTwoChannelPIMSDiscardedPayloadPacking hclosure where
  packConfig := rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity
  variable_eq :=
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq hcapacity
  reserved_open :=
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open hcapacity
  injective_on_fibre := by
    intro rho sigma htarget hpack
    let eta := rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho
    let rhoFibre : RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta := ⟨rho, rfl⟩
    let sigmaFibre : RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta :=
      ⟨sigma, htarget.symm⟩
    have hpackAt :
        rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta rhoFibre =
          rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta sigmaFibre :=
      (rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at
        hcapacity eta rhoFibre).symm.trans <|
        hpack.trans <|
          rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at
            hcapacity eta sigmaFibre
    have hbits :
        rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
            hcapacity eta rhoFibre =
          rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
            hcapacity eta sigmaFibre := by
      funext e
      have happ := congrFun hpackAt e.1.1
      simp only [rlc_twoChannelPIMSFixedPayloadConfigAt] at happ
      simp only [dif_neg e.1.2, dif_neg e.2] at happ
      simpa only [eta, rhoFibre, sigmaFibre] using happ
    have hfibre :=
      (rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
        hcapacity eta).injective hbits
    exact congrArg (fun fibre => fibre.1) hfibre

end
end StatMech.Universality
