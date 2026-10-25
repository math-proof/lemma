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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part72
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


def RlcRightEnvelopeProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ lambda : RlcRightDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        rlc_rightExploredVertices lambda ⊆
          rlc_rightExploredVertices gamma ∩
            rlc_rightExploredVertices delta


def RlcLeftEnvelopeProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcLeftDiagonalPath n,
    ∃ lambda : RlcLeftDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        rlc_leftExploredVertices lambda ⊆
          rlc_leftExploredVertices gamma ∩
            rlc_leftExploredVertices delta


def RlcRightFrontierPathProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ lambda : RlcRightDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        Disjoint (rlc_strictTopSet gamma ∪ rlc_strictTopSet delta)
          (rlc_pathVertices lambda.1 : Set (Site 2))

def RlcLeftFrontierPathProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcLeftDiagonalPath n,
    ∃ lambda : RlcLeftDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        Disjoint (rlc_strictBottomSet gamma ∪ rlc_strictBottomSet delta)
          (rlc_pathVertices lambda.1 : Set (Site 2))


end Universality
end StatMech
