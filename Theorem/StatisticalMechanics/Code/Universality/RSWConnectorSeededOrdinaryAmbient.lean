/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorMassDualityScaleOneAudit
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraphRepair
import Def.StatisticalMechanics.Code.Universality.RSWConnectorSeededOrdinaryAmbient
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_axisGapAmbientMixedConfig_supportEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_axisGapEdges G) :
    rlc_axisGapAmbientMixedConfig G tau e =
      tau (rlc_axisGapEdgeLift G e he) := by
  simp [rlc_axisGapAmbientMixedConfig, he]

@[simp] theorem rlc_axisGapAmbientMixedConfig_traceEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1))
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_axisGapAmbientMixedConfig G tau e = true := by
  have hnot : e ∉ rlc_axisGapEdges G := by
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_axisGapEdges G hdisj) hright
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_axisGapEdges G hdisj) hleft
  simp [rlc_axisGapAmbientMixedConfig, hnot, he]

@[simp] theorem rlc_axisGapAmbientMixedConfig_exterior {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (hG : e ∉ rlc_axisGapEdges G)
    (htrace : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_axisGapAmbientMixedConfig G tau e = false := by
  simp [rlc_axisGapAmbientMixedConfig, hG, htrace]


end
end StatMech.Universality
