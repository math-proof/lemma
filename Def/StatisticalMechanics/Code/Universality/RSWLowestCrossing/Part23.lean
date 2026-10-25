/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part23
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_rot180LeftPath {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : RlcRightDiagonalPath n := by
  let x : leftSide 0 (2 * n) (-n) n :=
    ⟨rlc_rot180 (gamma.1.2.1 : Site 2), by
      rw [mem_leftSide]
      have hy := gamma.1.2.1.2
      rw [mem_rightSide] at hy
      refine ⟨(rlc_rot180_mem_leftRect_iff_rightRect n _).mp hy.1, ?_⟩
      simpa using congrArg Neg.neg hy.2⟩
  let y : rightSide 0 (2 * n) (-n) n :=
    ⟨rlc_rot180 (gamma.1.1 : Site 2), by
      rw [mem_rightSide]
      have hx := gamma.1.1.2
      rw [mem_leftSide] at hx
      refine ⟨(rlc_rot180_mem_leftRect_iff_rightRect n _).mp hx.1, ?_⟩
      simpa using congrArg Neg.neg hx.2⟩
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180LeftInducedHom n)
  have hw : w.IsPath := by
    exact gamma.1.2.2.1.reverse.map_isPath_of_injective
      (rlc_rot180LeftInducedHom_injective n) gamma.1.2.2.2.reverse
  refine ⟨⟨x, y, ⟨w, hw⟩⟩, ?_, ?_⟩
  · change -(gamma.1.2.1 : Site 2) 1 ≤ 0
    exact neg_nonpos.mpr gamma.2.2
  · change 0 ≤ -(gamma.1.1 : Site 2) 1
    simpa [rlc_lowerHalf] using gamma.2.1

end Universality
end StatMech
