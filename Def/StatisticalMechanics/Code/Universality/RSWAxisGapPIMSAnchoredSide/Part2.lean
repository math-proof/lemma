/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSAnchoredSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcAxisGapPIMSFailureSelectedSideTopology {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) : Prop :=
  ∀ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    tau ∉ rlc_finiteAxisGapConnectorEvent G →
      RlcAxisGapPIMSAnchoredSideExists G hn hlt tau


def RlcAxisGapPIMSAnchoredContourSelector {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) : Prop :=
  ∀ (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))),
    tau ∉ rlc_finiteAxisGapConnectorEvent G →
      ∀ C : RlcAxisGapPIMSAnchoredContourCore G tau,
        Nonempty (RlcAxisGapPIMSAnchoredSelectedSide G hn hlt tau C)


end
end StatMech.Universality
