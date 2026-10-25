/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment


namespace StatMech.Universality

open HexWalk


def hlha_coordVertices (p d : HexReturnCoord) :
    List ℤ → List HexReturnCoord
  | [] => [p]
  | t :: ts =>
      p :: hlha_coordVertices (p.add (d.turn t)) (d.turn t) ts


def hlha_edgeVertices (p d : HexReturnCoord) :
    List ℤ → List HexReturnCoord
  | [] => [p, p.add d]
  | t :: ts =>
      p :: hlha_edgeVertices (p.add d) (d.turn t) ts

end StatMech.Universality
