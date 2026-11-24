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
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part32
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


def rlc_rightPathAvoidGraph {n : ℤ} (gamma : RlcRightDiagonalPath n) :
    SimpleGraph (Site 2) where
  Adj u v := (hypercubicLattice 2).Adj u v ∧
    u ∈ rect 0 (2 * n) (-n) n ∧ v ∈ rect 0 (2 * n) (-n) n ∧
    u ∉ rlc_pathVertices gamma.1 ∧ v ∉ rlc_pathVertices gamma.1
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

end Universality
end StatMech
