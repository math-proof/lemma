/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part4
open StatMech.FrontierD


namespace StatMech.FrontierD

structure AlignedExitRetie
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4) where
  pairingP : Bool
  pairingQ : Bool
  compatibleP : compatible pairingP p
  compatibleQ : compatible pairingQ q
  partnerDisagrees :
    p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))

end StatMech.FrontierD
