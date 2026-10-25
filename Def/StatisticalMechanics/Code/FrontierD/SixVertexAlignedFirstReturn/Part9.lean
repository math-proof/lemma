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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part7
open StatMech.FrontierD


namespace StatMech.FrontierD

noncomputable def orientedDartAlignedRetie
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    AlignedExitRetie
      (sixVertexLocalIncomingPattern omega d.1.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1.1) d.1.1.2 :=
  canonicalAlignedExitRetie
    (sixVertexLocalIncomingPattern omega d.1.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1.1) d.1.1.2
    (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
    (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
    (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
    (by
      have hd := sixVertexDisagreementDart_side_mem d.1
      rw [mem_sixVertexLocalDisagreementSides] at hd
      exact bne_iff_ne.mpr hd)

noncomputable def orientedDartAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) : Bool :=
  let retie := orientedDartAlignedRetie homega heta hdegree d
  if layer then retie.slotQ else retie.slotP


noncomputable def orientedDartBoundaryAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) : Bool :=
  let retie := orientedDartAlignedRetie homega heta hdegree d
  if layer then
    boundaryAlignedSlotQ (fkMedialVertexParity d.1.1.1) retie
  else retie.slotP

def orientedBlockVertices
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (block : List (SixVertexOrientedDisagreementDart omega eta)) :
    List T.Vertex :=
  block.map fun d => d.1.1.1

noncomputable def orientedBlockSlotOf
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (block : List (SixVertexOrientedDisagreementDart omega eta))
    (layer : Bool) (i : Fin (orientedBlockVertices block).length) : Bool :=
  let j : Fin block.length := ⟨i.val, by simpa [orientedBlockVertices] using i.isLt⟩
  orientedDartAlignedSlot homega heta hdegree layer (block.get j)

end StatMech.FrontierD
