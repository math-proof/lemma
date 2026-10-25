/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

def rlc_twoChannelPooledVisibleFibreEmbeddingOfGlobal
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (J : RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma')
    (hJ : forall rho,
      RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (J rho))
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      RlcTwoChannelSuccessVisibleFibre base where
  toFun rho := ⟨J rho.1, (hJ rho.1).trans rho.2⟩
  inj' := by
    intro rho sigma h
    apply Subtype.ext
    exact J.injective (congrArg Subtype.val h)


end
end StatMech.Universality
