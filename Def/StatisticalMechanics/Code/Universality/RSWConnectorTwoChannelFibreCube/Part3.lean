/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

def rlc_twoChannelFailureComplementFixedEmbedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma') where
  toFun rho := rlc_twoChannelFailureComplementFixedBits rho.1
  inj' := by
    intro rho sigma hbits
    apply
      (rlc_twoChannelFailureVisibleFibreDiscardedEmbedding base).injective
    funext e
    let f := (rlc_twoChannelPIMSFixedEquivDiscarded
      (gamma := gamma) (gamma' := gamma')).symm e
    have h := congrFun hbits f
    change Bool.not (rho.1.1
        (rlc_twoChannelPIMSFixedEquivDiscarded f).1) =
      Bool.not (sigma.1.1
        (rlc_twoChannelPIMSFixedEquivDiscarded f).1) at h
    have hval : (rlc_twoChannelPIMSFixedEquivDiscarded f).1 = e.1 :=
      congrArg Subtype.val
        ((rlc_twoChannelPIMSFixedEquivDiscarded
          (gamma := gamma) (gamma' := gamma')).apply_symm_apply e)
    rw [hval] at h
    exact Bool.not_injective h


def RlcTwoChannelFullPIMSPhysicalSuccess {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  forall rho : RlcTwoChannelEdgeFailure gamma gamma',
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPIMSConfig gamma gamma' rho.1) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma'


end
end StatMech.Universality
