/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part5
open MeasureTheory
open scoped BigOperators NNReal
open Finset


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}


@[simp]
theorem freeCorr_self (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a : {v // v ∈ S}) : freeCorr d β S a a = 1 := by
  simp [freeCorr]


theorem abs_freeCorr_le_one (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : |freeCorr d β S a b| ≤ 1 := by
  classical
  by_cases hab : a = b
  · simp [freeCorr, hab]
  rw [freeCorr, if_neg hab]
  unfold isingExpectation
  have hbound : ∀ s : ConfigSpace {v // v ∈ S}, |spinProd ({a, b} : Finset _) s| ≤ 1 := by
    intro s
    unfold spinProd
    rw [Finset.abs_prod]
    apply Finset.prod_le_one
    · intro x _; positivity
    · intro x _; exact abs_spin_le_one s x
  calc |∑ s : ConfigSpace {v // v ∈ S},
            isingProb (graphS d S) β 0 s * spinProd ({a, b} : Finset _) s|
      ≤ ∑ s : ConfigSpace {v // v ∈ S},
            |isingProb (graphS d S) β 0 s * spinProd ({a, b} : Finset _) s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : ConfigSpace {v // v ∈ S}, isingProb (graphS d S) β 0 s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul, abs_of_nonneg (isingProb_nonneg (graphS d S) β 0 s)]
        exact mul_le_mul_of_nonneg_left (hbound s) (isingProb_nonneg (graphS d S) β 0 s)
    _ = ∑ s : ConfigSpace {v // v ∈ S}, isingProb (graphS d S) β 0 s := by simp
    _ = 1 := isingProb_sum_eq_one (graphS d S) β 0


theorem freeCorr_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : 0 ≤ freeCorr d β S a b := by
  by_cases hab : a = b
  · simp [freeCorr, hab]
  rw [freeCorr, if_neg hab]
  exact gks_first (graphS d S) β 0 hβ le_rfl {a, b}


end Sharpness
end StatMech
