/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelClosureFailureCertificate_of_centralFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hcentral : RlcCentralFaceClosureFailureCertificate gamma gamma') :
    RlcTwoChannelClosureFailureCertificate gamma gamma' := by
  intro rho hno
  apply hcentral rho
  intro hcentralSuccess
  exact hno (rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel
    gamma gamma' hcentralSuccess)


theorem rlc_twoChannelPIMS_success_of_closureFailureCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
  rlc_centralFacePIMS_twoChannel_success_of_closure gamma gamma' rho
    (hfailure rho hno)

theorem rlc_finiteTwoChannelConnectorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  intro rho rho' hrho
  rintro ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, hxy.mono (FK.openSub_mono _ hrho)⟩


end
end StatMech.Universality
