/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelPIMSFixedRouteSourceDetermined {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') : Prop :=
  ∀ rho sigma : RlcTwoChannelEdgeFailure gamma gamma',
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho =
        rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma →
      ∀ e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma',
        e.1 ∈ rlc_twoChannelOpenEdgeSet
          (rlc_twoChannelCanonicalRoute
            (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1 →
        rho.1 (rlc_twoChannelPIMSEdgePerm gamma gamma' e.1) =
          sigma.1 (rlc_twoChannelPIMSEdgePerm gamma gamma' e.1)


noncomputable def rlc_twoChannelPIMSTargetFibreDiscardedEmbedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta ↪
      ConfigSpace (RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma') where
  toFun rho e := rho.1.1 e.1
  inj' := by
    intro rho sigma hbits
    apply Subtype.ext
    apply Subtype.ext
    apply
      rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
    apply Prod.ext
    · calc
        rlc_twoChannelPIMSEdgeProjection gamma gamma' rho.1.1 =
            (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho.1).1 := by
          rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val]
        _ = eta.1 := congrArg Subtype.val rho.2
        _ = (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma.1).1 :=
          (congrArg Subtype.val sigma.2).symm
        _ = rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma.1.1 := by
          rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val]
    · funext e
      exact congrFun hbits e


def RlcTwoChannelPIMSFixedPayloadCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') : Prop :=
  ∀ eta : RlcTwoChannelEdgeSuccess gamma gamma',
    Nat.card (RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta) ≤
    Nat.card (ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
      (rlc_twoChannelCanonicalRoute eta)))


noncomputable def rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta ↪
      ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
        (rlc_twoChannelCanonicalRoute eta)) := by
  letI := Fintype.ofFinite (RlcTwoChannelTargetFibre
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta)
  letI := Fintype.ofFinite (ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
    (rlc_twoChannelCanonicalRoute eta)))
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Nat.card_eq_fintype_card] using hcapacity eta


noncomputable def rlc_twoChannelPIMSFixedPayloadConfigAt {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta) :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  let bits := rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
    hcapacity eta rho
  fun e =>
    if hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
        rlc_connectorCentralFaceEdges gamma gamma' then
      eta.1 e
    else if hroute : e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute eta).1 then
      true
    else
      bits ⟨⟨e, hvariable⟩, hroute⟩


noncomputable def rlc_twoChannelPIMSFixedPayloadConfigOfCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho) ⟨rho, rfl⟩

end
end StatMech.Universality
