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
import Instance.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part4
open StatMech.FrontierD


namespace ScratchLocalRetieC

namespace FourByTwoBondAudit

def arrowsOfMask (mask : Nat) :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := Nat.testBit mask (v.2.val * 4 + v.1.val)
  vertical v := Nat.testBit mask (8 + v.2.val * 4 + v.1.val)

def omega : SixVertexArrows sixVertexFourByTwoTorus := arrowsOfMask 255

def eta : SixVertexArrows sixVertexFourByTwoTorus := arrowsOfMask 23205

def cutVertex : sixVertexFourByTwoTorus.Vertex :=
  sixVertexFourByTwoVertex 0 0


def singletonPrefixLocalPair
    (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  if v = cutVertex then
    exchangeLocalAlignedMask true false false false
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)
  else
    (sixVertexLocalIncomingPattern omega v,
      sixVertexLocalIncomingPattern eta v)

def singletonPrefixPattern
    (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern :=
  if layer then (singletonPrefixLocalPair v).2
  else (singletonPrefixLocalPair v).1

end FourByTwoBondAudit
end ScratchLocalRetieC
