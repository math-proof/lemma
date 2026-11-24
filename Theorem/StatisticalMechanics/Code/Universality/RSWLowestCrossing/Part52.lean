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
public import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part51
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


theorem rlc_path_start_mem_vertices {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) :
    (gamma.1 : Site 2) ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩,
    gamma.2.2.1.start_mem_support, rfl⟩

theorem rlc_rightPathStrictlyBelow_irrefl {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    ¬ rlc_rightPathStrictlyBelow gamma gamma := by
  intro h
  have hstart := rlc_path_start_mem_vertices gamma.1
  exact (Set.disjoint_left.mp (rlc_strictBelowSet_disjoint_path gamma))
    (h hstart) hstart

theorem rlc_leftPathStrictlyAbove_irrefl {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    ¬ rlc_leftPathStrictlyAbove gamma gamma := by
  intro h
  have hstart := rlc_path_start_mem_vertices gamma.1
  exact (Set.disjoint_left.mp (rlc_strictAboveSet_disjoint_path gamma))
    (h hstart) hstart

end Universality
end StatMech
