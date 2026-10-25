/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part5
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem localCIndicator_exchange_aligned_exit
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalCIndicator
        (strandSlot pairingP d)
        (strandSlot pairingQ
          (localMate pairingQ (localMate pairingP d))) p q =
      localCIndicator p + localCIndicator q := by
  unfold compatible exchangedLocalCIndicator exchangeLocalSlots
    localCIndicator horizontalSlot strandSlot localMate at *
  decide +revert


theorem exists_compatible_aligned_exit_pairings
    (p q : SixVertexLocalIncomingPattern)
    (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) :
    exists pairingP pairingQ : Bool,
      compatible pairingP p /\ compatible pairingQ q /\
        p (localMate pairingQ (localMate pairingP d)) !=
          q (localMate pairingQ (localMate pairingP d)) := by
  unfold compatible localMate at *
  decide +revert

end ScratchLocalRetieC
