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
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part25
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


noncomputable def rlc_swapRightInducedHom (n : ℤ) :
    ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)) →g
      hypercubicLattice 2 where
  toFun z := crf_swap (z : Site 2)
  map_rel' := by
    intro x y hxy
    exact (crf_adj_swap (x : Site 2) (y : Site 2)).mp hxy


noncomputable def rlc_swappedRightPathWalk {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    (hypercubicLattice 2).Walk
      (crf_swap (gamma.1.1 : Site 2))
      (crf_swap (gamma.1.2.1 : Site 2)) :=
  gamma.1.2.2.1.map (rlc_swapRightInducedHom n)


def rlc_swappedRightPathSupport {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Set (Site 2) :=
  {p | ∃ z ∈ gamma.1.2.2.1.support,
    p = crf_swap (z : Site 2)}


end Universality
end StatMech
