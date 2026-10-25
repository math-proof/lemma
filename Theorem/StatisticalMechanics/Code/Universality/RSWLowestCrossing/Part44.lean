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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part43
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_leftLowerUnionSet_finite {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) :
    (rlc_leftLowerUnionSet gamma delta).Finite :=
  (rlc_strictBottomSet_finite gamma).union
    (rlc_strictBottomSet_finite delta)

theorem rlc_leftLowerUnionSet_boundary_paths {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_leftLowerUnionSet gamma delta) s(u, v)) :
    (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨
      (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
  rcases rlc_bdEdge_union hbd with hgamma | hdelta
  · exact Or.inl (rlc_strictBottomSet_boundary_path gamma huR hvR hadj hgamma)
  · exact Or.inr (rlc_strictBottomSet_boundary_path delta huR hvR hadj hdelta)

theorem rlc_leftLowerUnionSet_exit_mem_paths {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_leftLowerUnionSet gamma delta)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hv : v ∉ rlc_leftLowerUnionSet gamma delta)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
  rcases hu with huGamma | huDelta
  · have hvGamma : v ∉ rlc_strictBottomSet gamma := fun h => hv (Or.inl h)
    have hbd : bdEdge (rlc_strictBottomSet gamma) s(u, v) := by
      rw [bdEdge_mk]
      exact iff_of_true huGamma hvGamma
    rcases rlc_strictBottomSet_boundary_path gamma
        (rlc_strictBottomSet_subset_box gamma huGamma) hvR hadj hbd with huP | hvP
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictBottomSet_disjoint_path gamma)) huGamma huP)
    · exact Or.inl hvP
  · have hvDelta : v ∉ rlc_strictBottomSet delta := fun h => hv (Or.inr h)
    have hbd : bdEdge (rlc_strictBottomSet delta) s(u, v) := by
      rw [bdEdge_mk]
      exact iff_of_true huDelta hvDelta
    rcases rlc_strictBottomSet_boundary_path delta
        (rlc_strictBottomSet_subset_box delta huDelta) hvR hadj hbd with huP | hvP
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictBottomSet_disjoint_path delta)) huDelta huP)
    · exact Or.inr hvP


end Universality
end StatMech
