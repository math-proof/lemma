/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part3
open MeasureTheory


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


@[simp] theorem isingAbsSite_nonneg (x : Site d) (a : Fin d) :
    0 <= isingAbsSite x a := abs_nonneg _

theorem isingSignNormalize_self (x : Site d) :
    isingSignNormalize x x = isingAbsSite x := by
  funext a
  by_cases ha : x a < 0
  · simp [isingSignNormalize, isingAbsSite, ha, abs_of_neg ha]
  · simp [isingSignNormalize, isingAbsSite, ha,
      abs_of_nonneg (le_of_not_gt ha)]

theorem currentContinuityFreeTwoPoint_absSite
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingAbsSite x) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have h := integral_freeState_spinProd_boxAutomorphism
    (isingSignNormalizeEquiv x)
    (hypercubicLattice_adj_signNormalize x)
    (mem_boxFinset_signNormalize_iff x)
    beta hbeta ({Percolation.origin d, x} : Finset (Site d))
  have ho : isingSignNormalize x (Percolation.origin d) =
      Percolation.origin d := by
    funext a
    by_cases ha : x a < 0 <;>
      simp [isingSignNormalize, Percolation.origin, ha]
  simp [isingSignNormalizeEquiv] at h
  rw [ho, isingSignNormalize_self] at h
  simpa [currentContinuityFreeTwoPoint] using h


end StatMech.FrontierA
