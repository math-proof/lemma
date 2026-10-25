/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part9
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


inductive PreferenceRightFlagChain {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    PreferenceTriangle n m → Prop
  | last {t : PreferenceTriangle n m} {k : Fin 3}
      (active : preferenceTriangleSideActive color t k)
      (toRight : preferenceTriangleOther t k = .right) :
      PreferenceRightFlagChain color t
  | cons {t s : PreferenceTriangle n m} {k : Fin 3}
      (active : preferenceTriangleSideActive color t k)
      (toNext : preferenceTriangleOther t k = .triangle s)
      (tail : PreferenceRightFlagChain color s) :
      PreferenceRightFlagChain color t

end StatMech.FK.PeriodicPlanar
