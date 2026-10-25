/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcAxisGapPIMSBoundaryArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)
      let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual
        G hn hlt (rlc_axisGapAmbientConfig G tau)
      ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
        e ∈ rlc_axisGapEdges G


def rlc_axisGapPIMSSelectedSideEvent {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {tau | RlcAxisGapPIMSBoundaryArc G hn hlt tau}


def RlcAxisGapPIMSActualSelectedArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)))).Walk x y),
    x ∈ rlc_pathVertices gamma.1 ∧
      y ∈ rlc_pathVertices gamma'.1 ∧
      (∀ z ∈ c.support,
        z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))) ∧
      (∀ e ∈ c.edges, e ∈ rlc_axisGapEdges G) ∧
      ∀ e ∈ c.edges, RlcAxisGapPIMSSourceOpenCase G tau e

end
end StatMech.Universality
