/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Def.StatisticalMechanics.Code.Universality.HexStripCountsClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hsc_negTurns_nil : hsc_negTurns [] = [] := rfl

@[simp] theorem hsc_negTurns_cons (t : ℤ) (ts : List ℤ) :
    hsc_negTurns (t :: ts) = (-t) :: hsc_negTurns ts := rfl

@[simp] theorem hsc_negTurns_length (ts : List ℤ) :
    (hsc_negTurns ts).length = ts.length := by simp [hsc_negTurns]


theorem hsc_negTurns_negTurns (ts : List ℤ) : hsc_negTurns (hsc_negTurns ts) = ts := by
  simp [hsc_negTurns, List.map_map]


end StatMech.Universality
