/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedExplorationBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcBookFaithfulExtremalTracePair.sequentialComparison_closed
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma')
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma'
        hfaith.toSequentialExplorationState.rawConfig e = false :=
  rlc_sequentialExtremalClosedComparison_of_mem _ he


theorem RlcBookFaithfulExtremalTracePair.sequentialComparison_agrees
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma')
    {e : Sym2 (Site 2)}
    (he : e ∉ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma'
        hfaith.toSequentialExplorationState.rawConfig e =
      hfaith.toSequentialExplorationState.rawConfig e :=
  rlc_sequentialExtremalClosedComparison_of_not_mem _ he

end
end StatMech.Universality
