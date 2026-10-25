/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part6
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable instance preferenceInterfaceGraph_decidableAdj {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    DecidableRel (preferenceInterfaceGraph color).Adj :=
  Classical.decRel _

end StatMech.FK.PeriodicPlanar
