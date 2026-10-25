/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelIndexedOuterEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  if h : RlcTwoChannelIndexedRetainedEdge gamma gamma' f then
    h.choose.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma')
  else
    s(rlc_twoChannelIndexedOuterPort gamma gamma' f false,
      rlc_twoChannelIndexedOuterPort gamma gamma' f true)


noncomputable def rlc_twoChannelIndexedAugmentedEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
  let source := rlc_twoChannelFullSourceEdge target
  ⟨source.1, SimpleGraph.edgeSet_mono le_sup_left source.2⟩

end
end StatMech.Universality
