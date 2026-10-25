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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part53
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_rightPathIndex {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : ℕ :=
  (Fintype.equivFin (RlcRightDiagonalPath n) gamma).val

noncomputable def rlc_leftPathIndex {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : ℕ :=
  (Fintype.equivFin (RlcLeftDiagonalPath n) gamma).val

noncomputable def rlc_rightPathRank {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : ℕ :=
  (rlc_rightExploredVertices gamma).card *
      Fintype.card (RlcRightDiagonalPath n) + rlc_rightPathIndex gamma

noncomputable def rlc_leftPathRank {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : ℕ :=
  (rlc_leftExploredVertices gamma).card *
      Fintype.card (RlcLeftDiagonalPath n) + rlc_leftPathIndex gamma


def rlc_rightPathBelow {n : ℤ}
    (delta gamma : RlcRightDiagonalPath n) : Prop :=
  rlc_rightExploredVertices delta ⊂ rlc_rightExploredVertices gamma ∨
    (rlc_rightExploredVertices delta = rlc_rightExploredVertices gamma ∧
      rlc_rightPathIndex delta < rlc_rightPathIndex gamma)


def rlc_leftPathAbove {n : ℤ}
    (delta gamma : RlcLeftDiagonalPath n) : Prop :=
  rlc_leftExploredVertices delta ⊂ rlc_leftExploredVertices gamma ∨
    (rlc_leftExploredVertices delta = rlc_leftExploredVertices gamma ∧
      rlc_leftPathIndex delta < rlc_leftPathIndex gamma)

end Universality
end StatMech
