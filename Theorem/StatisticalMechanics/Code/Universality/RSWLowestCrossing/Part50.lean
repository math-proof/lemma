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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part49
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_commonStrictAboveSet_finite {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) :
    (rlc_commonStrictAboveSet gamma delta).Finite :=
  (rlc_strictAboveSet_finite gamma).inter_of_left
    (rlc_strictAboveSet delta)

theorem rlc_top_mem_commonStrictAboveSet {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ topSide (-2 * n) 0 (-n) n)
    (hgamma : z ∉ rlc_pathVertices gamma.1)
    (hdelta : z ∉ rlc_pathVertices delta.1) :
    z ∈ rlc_commonStrictAboveSet gamma delta := by
  exact ⟨⟨z, hz, hgamma, SimpleGraph.Reachable.refl z⟩,
    ⟨z, hz, hdelta, SimpleGraph.Reachable.refl z⟩⟩

theorem rlc_leftBottomSide_disjoint_commonStrictAboveSet {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcLeftDiagonalPath n) :
    Disjoint (bottomSide (-2 * n) 0 (-n) n)
      (rlc_commonStrictAboveSet gamma delta) := by
  rw [Set.disjoint_left]
  intro z hzBottom hzCommon
  exact (Set.disjoint_left.mp
    (rlc_leftBottomSide_disjoint_strictAboveSet hn gamma)) hzBottom hzCommon.1

theorem rlc_commonStrictAboveSet_boundary_paths {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_commonStrictAboveSet gamma delta) s(u, v)) :
    (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨
      (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
  rcases rlc_bdEdge_inter hbd with hgamma | hdelta
  · exact Or.inl (rlc_strictAboveSet_boundary_path gamma huR hvR hadj hgamma)
  · exact Or.inr (rlc_strictAboveSet_boundary_path delta huR hvR hadj hdelta)

end Universality
end StatMech
