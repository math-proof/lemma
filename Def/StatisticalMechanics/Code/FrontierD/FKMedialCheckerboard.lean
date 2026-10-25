/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount


namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialSideVertical : FKMedialSide → Bool
  | .west | .east => false
  | .south | .north => true


def fkMedialVertexParity (v : T.Vertex) : Bool :=
  decide (Even v.1.val) ^^ decide (Even v.2.val)


def fkMedialCheckerColor (d : FKMedialDart T) : Bool :=
  fkMedialVertexParity d.1 ^^ fkMedialSideVertical d.2

end StatMech.FrontierD
