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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part36
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_leftPathAvoidGraph_walk_dest {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {x z : Site 2}
    (hxR : x ∈ rect (-2 * n) 0 (-n) n)
    (hxP : x ∉ rlc_pathVertices gamma.1)
    (w : (rlc_leftPathAvoidGraph gamma).Walk x z) :
    z ∈ rect (-2 * n) 0 (-n) n ∧ z ∉ rlc_pathVertices gamma.1 := by
  induction w with
  | nil => exact ⟨hxR, hxP⟩
  | @cons a b c hab w ih =>
      exact ih hab.2.2.1 hab.2.2.2.2


end Universality
end StatMech
