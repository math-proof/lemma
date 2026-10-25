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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part70
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


def RlcRightCanonicalAnchorReachability (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ y : rightSide 0 (2 * n) (-n) n,
      (y : Site 2) ∈ rlc_upperHalf ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨rlc_rightLeftTraceMinSide gamma delta,
          leftSide_subset (rlc_rightLeftTraceMinSide gamma delta).2⟩
        ⟨y, rightSide_subset y.2⟩


end Universality
end StatMech
