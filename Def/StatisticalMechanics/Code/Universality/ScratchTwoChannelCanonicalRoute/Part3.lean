/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelPIMSVariableVisibleEquiv {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    RlcTwoChannelPIMSVariableTargetEdge gamma gamma' ≃
      RlcTwoChannelPIMSVisibleSourceEdge gamma gamma' :=
  Equiv.ofInjective rlc_twoChannelPIMSSourceEdge
    rlc_twoChannelPIMSSourceEdge_injective


noncomputable def rlc_twoChannelPIMSEdgePerm {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Equiv.Perm (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
  (rlc_twoChannelPIMSVariableVisibleEquiv
    (gamma := gamma) (gamma' := gamma')).extendSubtype

end
end StatMech.Universality
