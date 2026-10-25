/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


@[simp] theorem isingMergeCoordinates_apply_i
    (i j : Fin d) (x : Site d) :
    isingMergeCoordinates i j x i = x i + x j := by
  simp [isingMergeCoordinates]

@[simp] theorem isingMergeCoordinates_apply_j
    (i j : Fin d) (hij : i ≠ j) (x : Site d) :
    isingMergeCoordinates i j x j = 0 := by
  rw [isingMergeCoordinates]
  simp only [if_neg (Ne.symm hij), if_pos]

theorem isingDiagonalReflect_self_eq_merge
    (i j : Fin d) (hij : i ≠ j) (x : Site d) :
    isingDiagonalReflect i j (x i) x = isingMergeCoordinates i j x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [hij, add_comm]
  · by_cases haj : a = j
    · subst a
      simp [hij, Ne.symm hij]
    · rw [isingDiagonalReflect_apply_of_ne i j a hai haj]
      simp [isingMergeCoordinates, hai, haj]


theorem currentContinuityFreeTwoPoint_mergeCoordinates_le
    (i j : Fin d) (hij : i ≠ j)
    (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (hi : 0 < x i) (hj : 0 <= x j) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingMergeCoordinates i j x) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  rcases hj.eq_or_lt with hj0 | hjpos
  · have hjzero : x j = 0 := hj0.symm
    have hmerge : isingMergeCoordinates i j x = x := by
      funext a
      by_cases hai : a = i
      · subst a
        simp [hjzero]
      · by_cases haj : a = j
        · subst a
          simp [isingMergeCoordinates, Ne.symm hij, hjzero]
        · simp [isingMergeCoordinates, hai, haj]
    rw [hmerge]
  · rw [← isingDiagonalReflect_self_eq_merge i j hij x]
    apply currentContinuityFreeTwoPoint_diagonalReflect_le
      i j hij (x i) beta hbeta (Percolation.origin d) x
    · simpa [Percolation.origin] using hi
    · omega
    · intro h
      have hcoord := congrFun h i
      simp [Percolation.origin] at hcoord
      omega
    · intro h
      have hcoord := congrFun h i
      simp [Percolation.origin, hij] at hcoord
      omega

end StatMech.FrontierA
