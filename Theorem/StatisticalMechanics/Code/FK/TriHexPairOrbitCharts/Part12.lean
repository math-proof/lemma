/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part14
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem longPairDisplacement_nonnegative (n : Nat) :
    siteLexNonnegative (longPairDisplacement n) := by
  left
  simp only [longPairDisplacement, Matrix.cons_val_zero]
  exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg n) (by norm_num)

end StatMech.FK.PeriodicPlanar
