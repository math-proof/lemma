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
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_cornerReturn {n : ℤ}
    (x : topSide 0 (2 * n) (-n) n)
    (z : rightSide 0 (2 * n) (-n) n) :
    (hypercubicLattice 2).Walk (z : Site 2) (x : Site 2) := by
  have hz0 : (z : Site 2) 0 = 2 * n := z.2.2
  have hx1 : (x : Site 2) 1 = n := x.2.2
  have hz1le : (z : Site 2) 1 ≤ n := by
    have hzSide := z.2
    rw [mem_rightSide, mem_rect] at hzSide
    exact hzSide.1.2.2.2
  have hx0le : (x : Site 2) 0 ≤ 2 * n := by
    have hxSide := x.2
    rw [mem_topSide, mem_rect] at hxSide
    exact hxSide.1.2.1
  have hzNat : ((n + 1 - (z : Site 2) 1).toNat : ℤ) =
      n + 1 - (z : Site 2) 1 := by
    rw [Int.toNat_of_nonneg (by omega)]
  have hxNat : ((2 * n + 1 - (x : Site 2) 0).toNat : ℤ) =
      2 * n + 1 - (x : Site 2) 0 := by
    rw [Int.toNat_of_nonneg (by omega)]
  let s1 : (hypercubicLattice 2).Walk (z : Site 2)
      ![2 * n + 1, (z : Site 2) 1] :=
    (jec_hsegRight ((z : Site 2) 1) (2 * n) 1).copy
      (by ext i; fin_cases i <;> simp [hz0])
      (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk
      ![2 * n + 1, (z : Site 2) 1] ![2 * n + 1, n + 1] :=
    (jec_vsegUp (2 * n + 1) ((z : Site 2) 1)
      (n + 1 - (z : Site 2) 1).toNat).copy rfl
      (by
        ext i
        fin_cases i
        · simp
        · simp [hzNat])
  let s3 : (hypercubicLattice 2).Walk
      ![(x : Site 2) 0, n + 1] ![2 * n + 1, n + 1] :=
    (jec_hsegRight (n + 1) ((x : Site 2) 0)
      (2 * n + 1 - (x : Site 2) 0).toNat).copy rfl
      (by
        ext i
        fin_cases i
        · simp [hxNat]
        · simp)
  let s4 : (hypercubicLattice 2).Walk
      ![(x : Site 2) 0, n] ![(x : Site 2) 0, n + 1] :=
    (jec_vsegUp ((x : Site 2) 0) n 1).copy rfl
      (by ext i; fin_cases i <;> simp)
  exact s1.append (s2.append (s3.reverse.append
    (s4.reverse.copy rfl (by
      ext i
      fin_cases i
      · simp
      · simpa using hx1.symm))))


end Universality
end StatMech
