/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Def.StatisticalMechanics.Code.Universality.HexW1ExitGeom


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexW1Exit_singleton_uniqueInterior (a : ℂ) (h0 : ℤ) (h : ℤ)
    (hint : (fun m => m = a + HexWalk.halfStep h0) (a + HexWalk.halfStep h)) :
    HexWalk.halfStep h = HexWalk.halfStep ((h0 + 3) + 3) := by
  
  have hstep : HexWalk.halfStep h = HexWalk.halfStep h0 := add_left_cancel hint
  
  have hper : HexWalk.halfStep ((h0 + 3) + 3) = HexWalk.halfStep h0 := by
    rw [show ((h0 + 3) + 3 : ℤ) = h0 + 6 by ring]
    unfold HexWalk.halfStep; rw [hexUnit_add_six]
  rw [hstep, hper]


end StatMech.Universality
