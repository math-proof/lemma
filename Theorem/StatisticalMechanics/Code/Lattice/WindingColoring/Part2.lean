/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Def.StatisticalMechanics.Code.Lattice.WindingColoring.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem wcl_flipCount_parity_eq_of_closedEven (flip : Site 2 → Site 2 → Prop)
    (hce : wcl_ClosedEven flip) {x y : Site 2}
    (w₁ w₂ : (hypercubicLattice 2).Walk x y) :
    wcl_flipCount flip w₁ % 2 = wcl_flipCount flip w₂ % 2 := by
  have hloop : Even (wcl_flipCount flip (w₁.append w₂.reverse)) := hce _
  rw [wcl_flipCount_append, wcl_flipCount_reverse] at hloop
  rcases hloop with ⟨k, hk⟩
  omega


end Lattice
end StatMech
