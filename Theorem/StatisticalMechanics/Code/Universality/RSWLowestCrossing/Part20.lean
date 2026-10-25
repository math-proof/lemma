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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part19
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


@[simp] theorem rlc_rot180_zero (x : Site 2) : rlc_rot180 x 0 = -x 0 := by
  simp [rlc_rot180, rlc_rot180Fun]

@[simp] theorem rlc_rot180_one (x : Site 2) : rlc_rot180 x 1 = -x 1 := by
  simp [rlc_rot180, rlc_rot180Fun]

@[simp] theorem rlc_rot180_involutive (x : Site 2) :
    rlc_rot180 (rlc_rot180 x) = x := rlc_rot180.left_inv x

@[simp] theorem rlc_rot180Edge_involutive (e : Sym2 (Site 2)) :
    Sym2.map rlc_rot180 (Sym2.map rlc_rot180 e) = e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp

theorem rlc_adj_rot180 (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_rot180 x) (rlc_rot180 y) := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, rlc_rot180_zero,
    rlc_rot180_one]
  have h0 : (-x 0 - -y 0).natAbs = (x 0 - y 0).natAbs := by
    rw [show -x 0 - -y 0 = -(x 0 - y 0) by ring, Int.natAbs_neg]
  have h1 : (-x 1 - -y 1).natAbs = (x 1 - y 1).natAbs := by
    rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg]
  rw [h0, h1]

theorem rlc_rot180_mem_rightRect_iff_leftRect (n : ℤ) (x : Site 2) :
    x ∈ rect 0 (2 * n) (-n) n ↔
      rlc_rot180 x ∈ rect (-2 * n) 0 (-n) n := by
  simp only [mem_rect, rlc_rot180_zero, rlc_rot180_one]
  omega

end Universality
end StatMech
