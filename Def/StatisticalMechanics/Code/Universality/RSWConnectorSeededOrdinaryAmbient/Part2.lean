/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorMassDualityScaleOneAudit
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraphRepair
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededOrdinaryAmbient
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_axisGapPIMSMixedReflectedConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig
    (rlc_dualReflectConfig (rlc_axisGapAmbientMixedConfig G tau))

end
end StatMech.Universality
