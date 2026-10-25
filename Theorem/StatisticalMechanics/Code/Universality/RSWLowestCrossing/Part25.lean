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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part24
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_pathPairOpen_dependsOn {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    DependsOn ((rlc_pathPairOpen pair).indicator (fun _ => (1 : ℝ)))
      (rlc_pathPairEdges pair : Set (Sym2 (Site 2))) := by
  simpa only [rlc_pathPairOpen, rlc_pathPairEdges, Finset.coe_union] using
    dependsOn_inter (rlc_pathOpen_dependsOn pair.1.1)
      (rlc_pathOpen_dependsOn pair.2.1)


theorem rlc_iUnion_pathPairOpen (n : ℤ) :
    (⋃ pair : RlcDiagonalPathPair n, rlc_pathPairOpen pair) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  ext omega
  constructor
  · intro h
    obtain ⟨pair, hright, hleft⟩ := Set.mem_iUnion.mp h
    exact ⟨by
      rw [← rlc_iUnion_rightDiagonalPath]
      exact Set.mem_iUnion.mpr ⟨pair.1, hright⟩,
      by
        rw [← rlc_iUnion_leftDiagonalPath]
        exact Set.mem_iUnion.mpr ⟨pair.2, hleft⟩⟩
  · rintro ⟨hright, hleft⟩
    rw [← rlc_iUnion_rightDiagonalPath] at hright
    rw [← rlc_iUnion_leftDiagonalPath] at hleft
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp hright
    obtain ⟨gamma', hgamma'⟩ := Set.mem_iUnion.mp hleft
    exact Set.mem_iUnion.mpr ⟨(gamma, gamma'), hgamma, hgamma'⟩


end Universality
end StatMech
