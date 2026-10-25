/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

theorem hypercubicLattice_adj_coordinateNegate
    (i : Fin d) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj
        (isingCoordinateNegate i x) (isingCoordinateNegate i y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingCoordinateNegate i x a -
      isingCoordinateNegate i y a).natAbs) = 1
  have hsum :
      (∑ a, (isingCoordinateNegate i x a -
        isingCoordinateNegate i y a).natAbs) =
        ∑ a, (x a - y a).natAbs := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases hai : a = i
    · subst a
      simp only [isingCoordinateNegate_apply_same]
      rw [show -x i - -y i = -(x i - y i) by ring, Int.natAbs_neg]
    · simp [isingCoordinateNegate_apply_of_ne i a hai]
  rw [hsum]

theorem mem_boxFinset_coordinateNegate_iff
    (i : Fin d) (n : Nat) (x : Site d) :
    x ∈ boxFinset d n ↔ isingCoordinateNegate i x ∈ boxFinset d n := by
  simp only [mem_boxFinset, mem_box]
  constructor <;> intro hx a
  · by_cases hai : a = i
    · subst a
      simpa using hx i
    · simpa [isingCoordinateNegate_apply_of_ne i a hai] using hx a
  · have h := hx a
    by_cases hai : a = i
    · subst a
      simpa using h
    · simpa [isingCoordinateNegate_apply_of_ne i a hai] using h

theorem integral_freeState_spinProd_coordinateNegate
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (A : Finset (Site d)) :
    (∫ omega, spinProd
        (A.map (isingCoordinateNegateEquiv i).toEmbedding) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
  integral_freeState_spinProd_boxAutomorphism
    (isingCoordinateNegateEquiv i)
    (hypercubicLattice_adj_coordinateNegate i)
    (mem_boxFinset_coordinateNegate_iff i) beta hbeta A

theorem currentContinuityFreeTwoPoint_coordinateNegate
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingCoordinateNegate i x) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have h := integral_freeState_spinProd_coordinateNegate
    i beta hbeta ({Percolation.origin d, x} : Finset (Site d))
  have ho : isingCoordinateNegate i (Percolation.origin d) =
      Percolation.origin d := by
    funext a
    by_cases hai : a = i <;>
      simp [isingCoordinateNegate, Percolation.origin, hai]
  simp [isingCoordinateNegateEquiv] at h
  rw [ho] at h
  simpa [currentContinuityFreeTwoPoint] using h


theorem mem_boxFinset_diagonalReflect_zero_iff
    (i j : Fin d) (hij : i ≠ j) (n : Nat) (x : Site d) :
    x ∈ boxFinset d n ↔
      isingDiagonalReflect i j 0 x ∈ boxFinset d n := by
  simp only [mem_boxFinset, mem_box]
  constructor
  · intro hx a
    by_cases hai : a = i
    · subst a
      simpa [hij] using hx j
    · by_cases haj : a = j
      · subst a
        simpa [hij, Ne.symm hij] using hx i
      · simpa [isingDiagonalReflect_apply_of_ne i j a hai haj] using hx a
  · intro hx a
    have h := hx (Equiv.swap i j a)
    have hR := congrFun (isingDiagonalReflect_involutive i j hij 0 x) a
    rw [← hR]
    by_cases hai : a = i
    · subst a
      simpa [hij] using hx j
    · by_cases haj : a = j
      · subst a
        simpa [hij, Ne.symm hij] using hx i
      · simpa [isingDiagonalReflect_apply_of_ne i j a hai haj] using hx a

theorem currentContinuityFreeTwoPoint_coordinateSwap
    (i j : Fin d) (hij : i ≠ j)
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingDiagonalReflect i j 0 x) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have h := integral_freeState_spinProd_boxAutomorphism
    (isingDiagonalReflectEquiv i j hij 0)
    (hypercubicLattice_adj_diagonalReflect i j hij 0)
    (mem_boxFinset_diagonalReflect_zero_iff i j hij)
    beta hbeta ({Percolation.origin d, x} : Finset (Site d))
  have ho : isingDiagonalReflect i j 0 (Percolation.origin d) =
      Percolation.origin d := by
    funext a
    simp [isingDiagonalReflect, isingDiagonalShift, Percolation.origin]
  simp [isingDiagonalReflectEquiv] at h
  rw [ho] at h
  simpa [currentContinuityFreeTwoPoint] using h

end StatMech.FrontierA
