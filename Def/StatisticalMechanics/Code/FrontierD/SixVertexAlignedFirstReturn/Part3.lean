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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn
open StatMech.FrontierD


namespace StatMech.FrontierD

def strandSlot (pairing : Bool) (d : Fin 4) : Bool :=
  if pairing then ![false, true, false, true] d
  else ![false, true, true, false] d

def sideVertical (d : Fin 4) : Bool :=
  ![false, false, true, true] d

def horizontalSlot (p : SixVertexLocalIncomingPattern) (side : Bool) : Bool :=
  if side then p 1 else p 0

def localCIndicator (p : SixVertexLocalIncomingPattern) : Nat :=
  if p 0 = p 1 then 1 else 0

end StatMech.FrontierD
