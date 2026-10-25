/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part5
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceInterfaceGraph {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    SimpleGraph (PreferenceInterfaceNode n m) where
  Adj := preferenceInterfaceAdj color
  symm := by
    constructor
    rintro u v ⟨t, k, hk, huv | hvu⟩
    · exact ⟨t, k, hk, Or.inr huv⟩
    · exact ⟨t, k, hk, Or.inl hvu⟩
  loopless := ⟨by
    rintro u ⟨t, k, _hk, huu | huu⟩
    · exact preferenceTriangleOther_ne_self t k (huu.2.symm.trans huu.1)
    · exact preferenceTriangleOther_ne_self t k (huu.2.symm.trans huu.1)⟩

end StatMech.FK.PeriodicPlanar
