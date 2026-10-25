/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Abbrev.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence
open Finset Matrix


namespace StatMech.FrontierD

def fkConfigurationToMedialPairing (T : EvenTorus) :
    FKMedialConfiguration T ≃ FKMedialLoopPairing T := Equiv.refl _

def fkLoopWestIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  omega.horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)

def fkLoopEastIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  !omega.horizontal v

def fkLoopSouthIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  omega.vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)

def fkLoopNorthIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  !omega.vertical v


def fkLoopPairingCompatible (pairing : Bool)
    (omega : SixVertexArrows T) (v : T.Vertex) : Prop :=
  if pairing then
    fkLoopWestIncoming omega v ≠ fkLoopSouthIncoming omega v ∧
      fkLoopEastIncoming omega v ≠ fkLoopNorthIncoming omega v
  else
    fkLoopWestIncoming omega v ≠ fkLoopNorthIncoming omega v ∧
      fkLoopEastIncoming omega v ≠ fkLoopSouthIncoming omega v

end StatMech.FrontierD
