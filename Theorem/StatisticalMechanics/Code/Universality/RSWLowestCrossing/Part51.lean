module
public import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.Inequalities.Harris
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part50
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
