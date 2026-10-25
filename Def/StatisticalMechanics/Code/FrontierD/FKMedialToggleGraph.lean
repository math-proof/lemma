/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle.Part2
open SimpleGraph


namespace StatMech.FrontierD

def fkMedialWestDart (v : T.Vertex) : FKMedialDart T := (v, .west)

def fkMedialEastDart (v : T.Vertex) : FKMedialDart T := (v, .east)


def fkMedialOldLocalEdges (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    Set (Sym2 (FKMedialDart T)) :=
  {s(fkMedialWestDart v,
      fkMedialLocalMate pairing (fkMedialWestDart v)),
    s(fkMedialEastDart v,
      fkMedialLocalMate pairing (fkMedialEastDart v))}


def fkMedialNewLocalEdges (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    Set (Sym2 (FKMedialDart T)) :=
  {s(fkMedialWestDart v,
      fkMedialLocalMate (fkMedialTogglePairingAt pairing v)
        (fkMedialWestDart v)),
    s(fkMedialEastDart v,
      fkMedialLocalMate (fkMedialTogglePairingAt pairing v)
        (fkMedialEastDart v))}

end StatMech.FrontierD
