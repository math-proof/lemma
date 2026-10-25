/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcAxisGapPIMSSourceOpenCase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2)) : Prop :=
  (∃ hsource : rlc_pimsEdgeEquiv e ∈ rlc_axisGapEdges G,
      tau (rlc_axisGapEdgeLift G (rlc_pimsEdgeEquiv e) hsource) = false) ∨
    rlc_pimsEdgeEquiv e ∉ rlc_axisGapEdges G


end
end StatMech.Universality
