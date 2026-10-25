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
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part11
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem alignedMaskedTarget_localIncomingPattern
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hbond : AlignedMaskedBondConsistent
      homega heta hdegree select0 select1)
    (layer : Bool) (v : T.Vertex) :
    sixVertexLocalIncomingPattern
        (alignedMaskedTarget homega heta hdegree select0 select1 layer) v =
      alignedMaskedLocalPattern homega heta hdegree
        select0 select1 layer v := by
  apply localIncomingPattern_arrowsOfIncomingPatterns
  · exact hbond.1 layer
  · exact hbond.2 layer


theorem sixVertexPairTotalC_mono_of_alignedLocalMask
    {T : EvenTorus} {omega eta omega' eta' : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hactive : forall (v : T.Vertex)
      (hv : (sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 2),
      let d := orientedDisagreementDartAtActiveVertex
        homega heta v hv
      (sixVertexLocalIncomingPattern omega' v,
          sixVertexLocalIncomingPattern eta' v) =
        exchangeLocalAlignedMask (select0 v) (select1 v)
          (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
          (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
          (sixVertexLocalIncomingPattern omega v)
          (sixVertexLocalIncomingPattern eta v))
    (hinactive : forall (v : T.Vertex)
      (hv : (sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 0),
      (sixVertexLocalIncomingPattern omega' v,
          sixVertexLocalIncomingPattern eta' v) =
        (sixVertexLocalIncomingPattern omega v,
          sixVertexLocalIncomingPattern eta v)) :
    sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount omega' + sixVertexTorusCTypeCount eta' := by
  apply sixVertexPairTotalC_mono_of_local
  intro v
  rcases hdegree v with hzero | htwo
  · have h := hinactive v hzero
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    dsimp only at hfirst hsecond
    rw [hfirst, hsecond]
  · let d := orientedDisagreementDartAtActiveVertex
      homega heta v htwo
    have h := hactive v htwo
    change (sixVertexLocalIncomingPattern omega' v,
        sixVertexLocalIncomingPattern eta' v) =
      exchangeLocalAlignedMask (select0 v) (select1 v)
        (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
        (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) at h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    dsimp only at hfirst hsecond
    rw [hfirst, hsecond]
    exact orientedDartBoundaryAlignedMask_nondecreases_localC
      homega heta hdegree (select0 v) (select1 v) d

theorem alignedMaskedTarget_totalC_mono
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hbond : AlignedMaskedBondConsistent
      homega heta hdegree select0 select1) :
    sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree select0 select1 false) +
        sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree select0 select1 true) := by
  apply sixVertexPairTotalC_mono_of_alignedLocalMask
    homega heta hdegree select0 select1
  · intro v hv
    rw [alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond false v,
      alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond true v]
    simp [alignedMaskedLocalPattern, alignedMaskedLocalPair, hv]
  · intro v hv
    have hnot : Not ((sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 2) := by omega
    rw [alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond false v,
      alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond true v]
    simp [alignedMaskedLocalPattern, alignedMaskedLocalPair, hnot]

theorem localIncomingPattern_eq_of_disagreement_card_zero
    (p q : SixVertexLocalIncomingPattern)
    (hzero : (sixVertexLocalDisagreementSides p q).card = 0) :
    p = q := by
  funext d
  by_contra hne
  have hmem : d ∈ sixVertexLocalDisagreementSides p q :=
    (mem_sixVertexLocalDisagreementSides p q d).2 hne
  have hpos : 0 < (sixVertexLocalDisagreementSides p q).card :=
    Finset.card_pos.mpr ⟨d, hmem⟩
  omega


end ScratchLocalRetieC
