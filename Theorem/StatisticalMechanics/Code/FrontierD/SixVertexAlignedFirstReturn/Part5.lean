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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part6
open StatMech.FrontierD


namespace StatMech.FrontierD

theorem localMate_involutive (pairing : Bool) (d : Fin 4) :
    localMate pairing (localMate pairing d) = d := by
  cases pairing <;> fin_cases d <;> rfl


theorem AlignedExitRetie.common_exit
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) :
    localMate retie.pairingP d =
      localMate retie.pairingQ retie.partnerSide := by
  unfold AlignedExitRetie.partnerSide
  rw [localMate_involutive]

end StatMech.FrontierD
