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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part10
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


def rlc_lowerHalf : Set (Site 2) := {z | z 1 ≤ 0}

def rlc_upperHalf : Set (Site 2) := {z | 0 ≤ z 1}


def rlc_rightDiagonal (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n rlc_lowerHalf rlc_upperHalf

def rlc_rightToUpper (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n Set.univ rlc_upperHalf

def rlc_lowerToRight (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n rlc_lowerHalf Set.univ


def rlc_leftDiagonal (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent (-2 * n) 0 (-n) n rlc_lowerHalf rlc_upperHalf


end Universality
end StatMech
