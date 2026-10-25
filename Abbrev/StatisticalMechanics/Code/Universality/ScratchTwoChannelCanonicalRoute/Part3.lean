/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcTwoChannelPIMSDiscardedSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    e ∉ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))}

abbrev RlcTwoChannelPIMSFixedTargetEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∉
      rlc_connectorCentralFaceEdges gamma gamma'}

abbrev RlcTwoChannelPIMSVisibleSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    e ∈ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))}


end
end StatMech.Universality
