/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

def rlc_twoChannelSuccessVisibleFibreEquivFixedPayload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelSuccessVisibleFibre base ≃
      RlcTwoChannelSuccessFixedPayload base where
  toFun eta := ⟨fun e => eta.1.1 e.1, by
    have hconfig : rlc_twoChannelConfigOfVisibleFixed base
        (fun e => eta.1.1 e.1) = eta.1.1 := by
      funext e
      by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        have hbase := congrFun eta.2 v
        simpa [rlc_twoChannelConfigOfVisibleFixed, hvariable,
          rlc_twoChannelSuccessVisibleBase] using hbase.symm
      · simp [rlc_twoChannelConfigOfVisibleFixed, hvariable]
    rw [hconfig]
    exact eta.1.2⟩
  invFun bits :=
    ⟨⟨rlc_twoChannelConfigOfVisibleFixed base bits.1, bits.2⟩, by
      funext e
      exact rlc_twoChannelConfigOfVisibleFixed_variable base bits.1 e⟩
  left_inv eta := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
        rlc_connectorCentralFaceEdges gamma gamma'
    · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
        ⟨e, hvariable⟩
      have hbase := congrFun eta.2 v
      simpa [rlc_twoChannelConfigOfVisibleFixed, hvariable,
        rlc_twoChannelSuccessVisibleBase] using hbase.symm
    · simp [rlc_twoChannelConfigOfVisibleFixed, hvariable]
  right_inv bits := by
    apply Subtype.ext
    funext e
    exact rlc_twoChannelConfigOfVisibleFixed_fixed base bits.1 e


def rlc_twoChannelFailureVisibleFibreDiscardedEmbedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      ConfigSpace (RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma') where
  toFun rho e := rho.1.1 e.1
  inj' := by
    intro rho sigma hbits
    apply Subtype.ext
    apply Subtype.ext
    apply
      rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
    apply Prod.ext
    · funext e
      by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        have hrho := congrFun rho.2 v
        have hsigma := congrFun sigma.2 v
        change (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho.1).1 v.1 =
          base v at hrho
        change (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma.1).1 v.1 =
          base v at hsigma
        rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val] at hrho hsigma
        exact hrho.trans hsigma.symm
      · let f : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        exact rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq
          rho.1.1 sigma.1.1 f
    · funext e
      exact congrFun hbits e


def rlc_twoChannelFailureComplementFixedBits {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma') :=
  fun e => !(rho.1 (rlc_twoChannelPIMSFixedEquivDiscarded e).1)


end
end StatMech.Universality
