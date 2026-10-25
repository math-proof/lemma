/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorMassDualityScaleOneAudit
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraphRepair
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_axisGapAmbientMixedConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if he : e ∈ rlc_axisGapEdges G then
    tau (rlc_axisGapEdgeLift G e he)
  else if e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then true
  else false

end
end StatMech.Universality
