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
import Structure.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn
open StatMech.FrontierD


namespace ScratchLocalRetieC

noncomputable def canonicalAlignedExitRetie
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) : AlignedExitRetie p q d := by
  let hex := exists_compatible_aligned_exit_pairings
    p q d hp hq hdegree hd
  let pairingP := Classical.choose hex
  let hexQ := Classical.choose_spec hex
  let pairingQ := Classical.choose hexQ
  let hspec := Classical.choose_spec hexQ
  exact ⟨pairingP, pairingQ, hspec.1, hspec.2.1, hspec.2.2⟩

def AlignedExitRetie.slotP
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Bool :=
  strandSlot retie.pairingP d

def AlignedExitRetie.partnerSide
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Fin 4 :=
  localMate retie.pairingQ (localMate retie.pairingP d)

def AlignedExitRetie.slotQ
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Bool :=
  strandSlot retie.pairingQ retie.partnerSide

end ScratchLocalRetieC
