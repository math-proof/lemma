/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSSelectedSide.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part4
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSSelectedSide
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_maskConfig_axisGapAmbientConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_maskConfig (rlc_axisGapEdges G) (rlc_axisGapAmbientConfig G tau) =
      rlc_axisGapAmbientConfig G tau := by
  funext e
  by_cases he : e ∈ rlc_axisGapEdges G <;>
    simp [rlc_maskConfig, rlc_axisGapAmbientConfig, he]

theorem rlc_axisGapPIMSReflectedConfig_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Sym2 (RlcConnectorVertex n)) :
    rlc_axisGapPIMSReflectedConfig G tau f =
      !(rlc_axisGapAmbientConfig G tau
        (rlc_pimsEdgeEquiv (f.map Subtype.val))) := by
  unfold rlc_axisGapPIMSReflectedConfig rlc_connectorRestrictConfig
  rw [rlc_dualReflectConfig_eq_pims]


end
end StatMech.Universality
