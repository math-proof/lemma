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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part50
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


@[simp] theorem rlc_mem_strictBelowVertices {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictBelowVertices gamma ↔ z ∈ rlc_strictBelowSet gamma := by
  simp [rlc_strictBelowVertices]

@[simp] theorem rlc_mem_strictAboveVertices {n : ℤ}
    {gamma : RlcLeftDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictAboveVertices gamma ↔ z ∈ rlc_strictAboveSet gamma := by
  simp [rlc_strictAboveVertices]

@[simp] theorem rlc_mem_strictTopVertices {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictTopVertices gamma ↔ z ∈ rlc_strictTopSet gamma := by
  simp [rlc_strictTopVertices]

@[simp] theorem rlc_mem_strictBottomVertices {n : ℤ}
    {gamma : RlcLeftDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictBottomVertices gamma ↔ z ∈ rlc_strictBottomSet gamma := by
  simp [rlc_strictBottomVertices]


end Universality
end StatMech
