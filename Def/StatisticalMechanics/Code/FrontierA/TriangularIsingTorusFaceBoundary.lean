/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


def triangularFaceEastCoeff {L : Nat}
    (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) : Int :=
  (lower p).val - (upper (p.1, p.2 - 1)).val


def triangularFaceNorthCoeff {L : Nat}
    (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) : Int :=
  (lower (p.1 - 1, p.2)).val - (upper p).val


def triangularFaceDiagonalCoeff {L : Nat}
    (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) : Int :=
  (upper p).val - (lower p).val


def triangularFaceBoundaryCoeff {L : Nat}
    (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (d : triangularTorusDart L) : Int :=
  match d.2.val with
  | 0 => -triangularFaceEastCoeff lower upper (d.1.1 - 1, d.1.2)
  | 1 => triangularFaceEastCoeff lower upper d.1
  | 2 => -triangularFaceNorthCoeff lower upper (d.1.1, d.1.2 - 1)
  | 3 => triangularFaceNorthCoeff lower upper d.1
  | 4 => -triangularFaceDiagonalCoeff lower upper
      (d.1.1 - 1, d.1.2 - 1)
  | _ => triangularFaceDiagonalCoeff lower upper d.1

end StatMech.FrontierA
