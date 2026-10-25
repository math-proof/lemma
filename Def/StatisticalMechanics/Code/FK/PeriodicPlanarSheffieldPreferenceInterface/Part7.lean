/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part7
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceLeftTriangle {n m : Nat} (hn : 0 < n) (j : Fin m) :
    PreferenceTriangle n m :=
  ⟨⟨0, hn⟩, j, true⟩

noncomputable def preferenceLeftActiveRows {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j =>
    preferenceTriangleSideActive color (preferenceLeftTriangle hn j) 2

end StatMech.FK.PeriodicPlanar
