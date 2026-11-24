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
public import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part71
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


theorem rlc_leftSafeTraceGraph_walk_support_safe {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n)
    {x y : rect (-2 * n) 0 (-n) n}
    (w : (rlc_leftSafeTraceGraph gamma delta).Walk x y)
    (hx : (x : Site 2) ∉ rlc_leftLowerUnionSet gamma delta)
    {z : rect (-2 * n) 0 (-n) n} (hz : z ∈ w.support) :
    (z : Site 2) ∉ rlc_leftLowerUnionSet gamma delta := by
  induction w with
  | nil =>
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hx
  | @cons a b c hab w ih =>
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hab.2.2.1
      · exact ih hab.2.2.2 hz


end Universality
end StatMech
