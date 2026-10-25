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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part87
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


@[simp] theorem rlc_dualReflect_zero (x : Site 2) :
    rlc_dualReflect x 0 = -x 0 - 1 := by
  rfl

@[simp] theorem rlc_dualReflect_one (x : Site 2) :
    rlc_dualReflect x 1 = x 1 + 1 := by
  rfl

@[simp] theorem rlc_dualReflect_symm_zero (x : Site 2) :
    rlc_dualReflect.symm x 0 = -x 0 - 1 := by
  rfl

@[simp] theorem rlc_dualReflect_symm_one (x : Site 2) :
    rlc_dualReflect.symm x 1 = x 1 - 1 := by
  rfl


theorem rlc_adj_dualReflect (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_dualReflect x) (rlc_dualReflect y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_dualReflect_zero, rlc_dualReflect_one]
  rw [show (-x 0 - 1) - (-y 0 - 1) = -(x 0 - y 0) by ring,
    Int.natAbs_neg,
    show (x 1 + 1) - (y 1 + 1) = x 1 - y 1 by ring]


end Universality
end StatMech
