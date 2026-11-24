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
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part50
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


noncomputable def rlc_strictBelowVertices {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictBelowSet_finite gamma).toFinset

noncomputable def rlc_strictAboveVertices {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictAboveSet_finite gamma).toFinset

noncomputable def rlc_strictTopVertices {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictTopSet_finite gamma).toFinset

noncomputable def rlc_strictBottomVertices {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictBottomSet_finite gamma).toFinset

end Universality
end StatMech
