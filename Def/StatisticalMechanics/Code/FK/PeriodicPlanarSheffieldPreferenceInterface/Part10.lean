/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part10
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceGridSite {n m : Nat} (x : PreferenceGridVertex n m) : Site 2
  | 0 => x.1.val
  | 1 => x.2.val

def preferenceTriangleSideTrue {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) : PreferenceGridVertex n m :=
  if color (preferenceTriangleVertex t k) = true then
    preferenceTriangleVertex t k
  else
    preferenceTriangleVertex t (preferenceTriangleNext k)

def preferenceTriangleSideFalse {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) : PreferenceGridVertex n m :=
  if color (preferenceTriangleVertex t k) = true then
    preferenceTriangleVertex t (preferenceTriangleNext k)
  else
    preferenceTriangleVertex t k

end StatMech.FK.PeriodicPlanar
