/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
import Theorem.StatisticalMechanics.Code.Universality.QOneRSWActiveSeed.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorActualSelectedObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_scaleTwoAxisGapRestrictedConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 2)) :=
  rlc_connectorRestrictConfig rlc_scaleTwoDoubleFailureConfig


end
end StatMech.Universality
