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
import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part3
open StatMech.FrontierD


namespace ScratchLocalRetieC

def exchangeLocalSlots (sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun d =>
      if strandSlot false d = sideP then
        horizontalSlot q sideQ
      else p d,
   fun d =>
      if strandSlot false d = sideQ then
        horizontalSlot p sideP
      else q d)

def exchangedLocalCIndicator (sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) : Nat :=
  localCIndicator (exchangeLocalSlots sideP sideQ p q).1 +
    localCIndicator (exchangeLocalSlots sideP sideQ p q).2


def exchangeLocalAlignedMask (select0 select1 sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun d =>
      let branch := strandSlot false d != sideP
      let selected := if branch then select1 else select0
      let sourceQ := if branch then !sideQ else sideQ
      if selected then horizontalSlot q sourceQ else p d,
   fun d =>
      let branch := strandSlot false d != sideQ
      let selected := if branch then select1 else select0
      let sourceP := if branch then !sideP else sideP
      if selected then horizontalSlot p sourceP else q d)

def exchangedLocalAlignedMaskCIndicator
    (select0 select1 sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) : Nat :=
  localCIndicator
      (exchangeLocalAlignedMask select0 select1 sideP sideQ p q).1 +
    localCIndicator
      (exchangeLocalAlignedMask select0 select1 sideP sideQ p q).2


end ScratchLocalRetieC
