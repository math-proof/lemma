/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable def fkMedialLoopCount (T : EvenTorus)
    (pairing : FKMedialLoopPairing T) : Nat :=
  Nat.card (FKMedialLoop T pairing)


def fkMedialDartIncoming (omega : SixVertexArrows T)
    (d : FKMedialDart T) : Bool :=
  match d.2 with
  | .west => fkLoopWestIncoming omega d.1
  | .east => fkLoopEastIncoming omega d.1
  | .south => fkLoopSouthIncoming omega d.1
  | .north => fkLoopNorthIncoming omega d.1


end StatMech.FrontierD
