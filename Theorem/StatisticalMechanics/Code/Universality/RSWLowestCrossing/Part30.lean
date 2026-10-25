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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part29
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_swappedLeftBelowSet_spec {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    (∀ z : Site 2, z ∈ rect (-n) n (-2 * n) 0 → z 0 = -n →
      z ∈ rlc_swappedLeftBelowSet hn gamma) ∧
    (∀ z : Site 2, z ∈ rect (-n) n (-2 * n) 0 → z 0 = n →
      z ∉ rlc_swappedLeftBelowSet hn gamma) ∧
    (∀ u v : Site 2, u ∈ rect (-n) n (-2 * n) 0 →
      v ∈ rect (-n) n (-2 * n) 0 →
      (hypercubicLattice 2).Adj u v →
      bdEdge (rlc_swappedLeftBelowSet hn gamma) s(u, v) →
      u ∈ rlc_swappedLeftPathSupport gamma ∨
        v ∈ rlc_swappedLeftPathSupport gamma) :=
  Classical.choose_spec (rlc_leftPath_arcSeparatingSet hn gamma)


end Universality
end StatMech
