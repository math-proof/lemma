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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part71
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


def rlc_leftSafeTraceGraph {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) :
    SimpleGraph (rect (-2 * n) 0 (-n) n) where
  Adj u v :=
    ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Adj u v ∧
      s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
      (u : Site 2) ∉ rlc_leftLowerUnionSet gamma delta ∧
      (v : Site 2) ∉ rlc_leftLowerUnionSet gamma delta
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2.1,
      h.2.2.2, h.2.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def RlcLeftSafeTraceReachability (n : ℤ) : Prop :=
  ∀ gamma delta : RlcLeftDiagonalPath n,
    ∃ (x : leftSide (-2 * n) 0 (-n) n)
      (y : rightSide (-2 * n) 0 (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_leftLowerUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_leftLowerUnionSet gamma delta ∧
      (rlc_leftSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩

end Universality
end StatMech
