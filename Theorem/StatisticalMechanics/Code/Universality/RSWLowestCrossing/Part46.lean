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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part45
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightPairAvoidGraph_walk_dest {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {x z : Site 2}
    (hxR : x ∈ rect 0 (2 * n) (-n) n)
    (hxGamma : x ∉ rlc_pathVertices gamma.1)
    (hxDelta : x ∉ rlc_pathVertices delta.1)
    (w : (rlc_rightPairAvoidGraph gamma delta).Walk x z) :
    z ∈ rect 0 (2 * n) (-n) n ∧
      z ∉ rlc_pathVertices gamma.1 ∧
      z ∉ rlc_pathVertices delta.1 := by
  induction w with
  | nil => exact ⟨hxR, hxGamma, hxDelta⟩
  | @cons a b c hab w ih =>
      exact ih hab.2.2.1 hab.2.2.2.2.1 hab.2.2.2.2.2.2


end Universality
end StatMech
