/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology
open SimpleGraph


namespace StatMech.FrontierD

def fkMedialLocalMate (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) : FKMedialDart T :=
  match pairing d.1, d.2 with
  | false, .west => (d.1, .north)
  | false, .north => (d.1, .west)
  | false, .east => (d.1, .south)
  | false, .south => (d.1, .east)
  | true, .west => (d.1, .south)
  | true, .south => (d.1, .west)
  | true, .east => (d.1, .north)
  | true, .north => (d.1, .east)


def fkMedialBondMate (T : EvenTorus)
    (d : FKMedialDart T) : FKMedialDart T :=
  match d.2 with
  | .west =>
      ((SixVertexArrows.cyclicPred T.width_pos d.1.1, d.1.2), .east)
  | .east =>
      ((finitePeriodicSucc T.width_pos d.1.1, d.1.2), .west)
  | .south =>
      ((d.1.1, SixVertexArrows.cyclicPred T.height_pos d.1.2), .north)
  | .north =>
      ((d.1.1, finitePeriodicSucc T.height_pos d.1.2), .south)

end StatMech.FrontierD
