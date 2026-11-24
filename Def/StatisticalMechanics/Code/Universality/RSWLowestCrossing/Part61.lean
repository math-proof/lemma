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
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part61
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


def rlc_rightSafeTraceGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    SimpleGraph (rect 0 (2 * n) (-n) n) where
  Adj u v :=
    ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Adj u v ∧
      s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
      (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2.1,
      h.2.2.2, h.2.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

end Universality
end StatMech
