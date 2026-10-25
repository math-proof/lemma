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
open StatMech.FrontierD


namespace ScratchLocalRetieC

def localMate (pairing : Bool) (d : Fin 4) : Fin 4 :=
  if pairing then ![2, 3, 0, 1] d else ![3, 2, 1, 0] d

def compatible (pairing : Bool)
    (p : SixVertexLocalIncomingPattern) : Prop :=
  if pairing then p 0 != p 2 /\ p 1 != p 3
  else p 0 != p 3 /\ p 1 != p 2

end ScratchLocalRetieC
