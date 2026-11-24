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
public import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part52
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


theorem rlc_rightPathVertex_mem_explored {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_rightExploredVertices gamma := by
  rw [rlc_rightExploredVertices, Finset.mem_sdiff]
  constructor
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
    obtain ⟨u, _hu, rfl⟩ := hz
    simpa using u.2
  · intro hzTop
    exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path gamma))
      (by simpa using hzTop) hz

theorem rlc_leftPathVertex_mem_explored {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_leftExploredVertices gamma := by
  rw [rlc_leftExploredVertices, Finset.mem_sdiff]
  constructor
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
    obtain ⟨u, _hu, rfl⟩ := hz
    simpa using u.2
  · intro hzBottom
    exact (Set.disjoint_left.mp (rlc_strictBottomSet_disjoint_path gamma))
      (by simpa using hzBottom) hz

end Universality
end StatMech
