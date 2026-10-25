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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part68
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_rightCommonReverseRank {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta)) : ℕ := by
  have hz : (z.1 ∈ gamma.1.2.2.1.reverse.support) ∧
      (z.1 ∈ delta.1.2.2.1.reverse.support) := by
    have hz' := Finset.mem_inter.mp z.2
    constructor
    · simpa [SimpleGraph.Walk.support_reverse] using hz'.1
    · simpa [SimpleGraph.Walk.support_reverse] using hz'.2
  exact (gamma.1.2.2.1.reverse.takeUntil z.1 hz.1).length +
    (delta.1.2.2.1.reverse.takeUntil z.1 hz.2).length


noncomputable def rlc_rightCommonGammaReverseRank {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta)) : ℕ := by
  have hz : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    have hz' := (Finset.mem_inter.mp z.2).1
    simpa [SimpleGraph.Walk.support_reverse] using hz'
  exact (gamma.1.2.2.1.reverse.takeUntil z.1 hz).length


end Universality
end StatMech
