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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part9
open StatMech.FrontierD


namespace StatMech.FrontierD

noncomputable def alignedMaskedLocalPair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool) (v : T.Vertex) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    exchangeLocalAlignedMask (select0 v) (select1 v)
      (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
      (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)
  else
    (sixVertexLocalIncomingPattern omega v,
      sixVertexLocalIncomingPattern eta v)

noncomputable def alignedStateSelectorBranchMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (selected : DoubledAlignedState omega eta -> Bool)
    (branch : Bool) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    selected (orientedDisagreementDartAtActiveVertex
      homega heta v hv, branch)
  else false

def alignedStateListSelector
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (states : List (DoubledAlignedState omega eta))
    (x : DoubledAlignedState omega eta) : Bool :=
  decide (x ∈ states)

noncomputable def alignedStateListBranchMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (states : List (DoubledAlignedState omega eta))
    (branch : Bool) (v : T.Vertex) : Bool :=
  alignedStateSelectorBranchMask homega heta
    (alignedStateListSelector states) branch v

noncomputable def alignedMaskedLocalPattern
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (layer : Bool) (v : T.Vertex) : SixVertexLocalIncomingPattern :=
  if layer then
    (alignedMaskedLocalPair homega heta hdegree select0 select1 v).2
  else (alignedMaskedLocalPair homega heta hdegree select0 select1 v).1

noncomputable def alignedMaskedTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (layer : Bool) : SixVertexArrows T :=
  arrowsOfIncomingPatterns
    (alignedMaskedLocalPattern homega heta hdegree select0 select1 layer)

def AlignedMaskedBondConsistent
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool) : Prop :=
  (forall (layer : Bool) (v : T.Vertex),
    alignedMaskedLocalPattern homega heta hdegree
        select0 select1 layer v 0 =
      !alignedMaskedLocalPattern homega heta hdegree select0 select1 layer
        (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1) /\
  (forall (layer : Bool) (v : T.Vertex),
    alignedMaskedLocalPattern homega heta hdegree
        select0 select1 layer v 2 =
      !alignedMaskedLocalPattern homega heta hdegree select0 select1 layer
        (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) 3)

end StatMech.FrontierD
