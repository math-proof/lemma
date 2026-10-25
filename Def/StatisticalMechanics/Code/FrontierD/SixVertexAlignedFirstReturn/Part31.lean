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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part29
open StatMech.FrontierD


namespace StatMech.FrontierD

namespace FourByTwoPrefixBondAudit

def alignedSlot (v : sixVertexFourByTwoTorus.Vertex) : Bool :=
  decide ((v.1.val + v.2.val) % 2 = 1)

def maskedLocalPair
    (select0 select1 : sixVertexFourByTwoTorus.Vertex -> Bool)
    (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  exchangeLocalAlignedMask (select0 v) (select1 v)
    (alignedSlot v) (alignedSlot v)
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern eta v)

def maskedPattern
    (select0 select1 : sixVertexFourByTwoTorus.Vertex -> Bool)
    (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern :=
  if layer then (maskedLocalPair select0 select1 v).2
  else (maskedLocalPair select0 select1 v).1

def MaskedBondConsistent
    (select0 select1 : sixVertexFourByTwoTorus.Vertex -> Bool) : Prop :=
  (forall (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex),
    maskedPattern select0 select1 layer v 0 =
      !maskedPattern select0 select1 layer
        (SixVertexArrows.cyclicPred
          sixVertexFourByTwoTorus.width_pos v.1, v.2) 1) /\
  (forall (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex),
    maskedPattern select0 select1 layer v 2 =
      !maskedPattern select0 select1 layer
        (v.1, SixVertexArrows.cyclicPred
          sixVertexFourByTwoTorus.height_pos v.2) 3)


def selectorCharge
    (select0 : sixVertexFourByTwoTorus.Vertex -> Bool) : Nat :=
  (select0 (sixVertexFourByTwoVertex 0 0)).toNat +
    (select0 (sixVertexFourByTwoVertex 2 0)).toNat

end FourByTwoPrefixBondAudit
end StatMech.FrontierD
