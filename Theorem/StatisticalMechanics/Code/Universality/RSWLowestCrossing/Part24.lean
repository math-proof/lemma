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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part23
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_iUnion_rightDiagonalPath (n : ℤ) :
    (⋃ gamma : RlcRightDiagonalPath n, rlc_pathOpen gamma.1) =
      rlc_rightDiagonal n :=
  rlc_iUnion_restrictedPathOpen 0 (2 * n) (-n) n rlc_lowerHalf rlc_upperHalf

theorem rlc_iUnion_leftDiagonalPath (n : ℤ) :
    (⋃ gamma : RlcLeftDiagonalPath n, rlc_pathOpen gamma.1) =
      rlc_leftDiagonal n :=
  rlc_iUnion_restrictedPathOpen (-2 * n) 0 (-n) n rlc_lowerHalf rlc_upperHalf


end Universality
end StatMech
