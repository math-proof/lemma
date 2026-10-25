/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFaithfulAugmentedEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : RlcTwoChannelFaithfulSourceEdge gamma gamma') :
    Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
  ⟨e.1, SimpleGraph.edgeSet_mono le_sup_left e.2⟩


noncomputable def rlc_twoChannelFaithfulEnds {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFaithfulSourceEdge gamma gamma' →
      Sym2 (RlcTwoChannelFaithfulFace gamma gamma') :=
  fun e => Ising.kwg_dualEnds
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
    (rlc_twoChannelFaithfulAugmentedEdge e)

def rlc_twoChannelFaithfulDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (RlcTwoChannelFaithfulSourceEdge gamma gamma') :=
  fun e => !(omega e)

end
end StatMech.Universality
