/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part9


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhd_normalizeHeading (up : Bool) (h : Fin 6) : Fin 6 :=
  if up then h else h + 3


def hlhd_edgeOfHeading (c : HexAWCoord) (h : Fin 6) : Fin 3 :=
  match c.color, h.val with
  | .black, 4 => 0
  | .black, 0 => 1
  | .black, 2 => 2
  | .white, 1 => 0
  | .white, 3 => 1
  | .white, 5 => 2
  | _, _ => 0


def hlhd_coordPath : HexAWCoord → Fin 6 → List ℤ → List HexAWCoord
  | c, h, [] => [c, hexAWNeighbor c (hlhd_edgeOfHeading c h)]
  | c, h, t :: ts =>
      c :: hlhd_coordPath
        (hexAWNeighbor c (hlhd_edgeOfHeading c h))
        (hexHeadingTurn h t) ts

end
end StatMech.Universality
