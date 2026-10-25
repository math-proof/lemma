/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenBoxGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Def.StatisticalMechanics.Code.FrontierA.AllOpenBoxGeneral.Part2
open Set SimpleGraph Finset


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


theorem bgfd_idx_iff_inBox {L : ℕ} {j x : Site d} :
    bgn_idx L x = j ↔ bgfdInBox L (bgfdCentre L j) x := by
  constructor
  · intro h i
    have hxi : (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i := by
      rw [← h]
      rfl
    have hdiv := (bsc_ediv_eq_iff).mp hxi
    simpa [bgfdCentre] using hdiv
  · intro h
    funext i
    show (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i
    refine (bsc_ediv_eq_iff).mpr ?_
    simpa [bgfdCentre] using h i

theorem bgfd_idx_centre (L : ℕ) (j : Site d) :
    bgn_idx L (bgfdCentre L j) = j :=
  bgfd_idx_iff_inBox.mpr (by intro i; simp [bgfdCentre])

theorem bgfd_centre_injective (L : ℕ) :
    Function.Injective (bgfdCentre (d := d) L) := by
  intro j k h
  funext i
  have hi := congrFun h i
  simp only [bgfdCentre] at hi
  have hfactor : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hfactor hi


theorem bgfd_lat_shift (c x y : Site d) :
    (hypercubicLattice d).Adj (x + c) (y + c) ↔
      (hypercubicLattice d).Adj x y := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj]
  refine Iff.of_eq (congrArg (· = 1) ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]
  congr 1
  ring


theorem bgfd_idx_shift (L : ℕ) (j x : Site d) :
    bgn_idx L (x + bgfdCentre L j) = bgn_idx L x + j := by
  funext i
  have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  show ((x + bgfdCentre L j) i + (L : ℤ)) / (2 * (L : ℤ) + 1) =
    bgn_idx L x i + j i
  rw [Pi.add_apply]
  show (x i + bgfdCentre L j i + (L : ℤ)) /
      (2 * (L : ℤ) + 1) =
    (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) + j i
  have hc : bgfdCentre L j i = (2 * (L : ℤ) + 1) * j i := rfl
  rw [hc]
  have hrw : x i + (2 * (L : ℤ) + 1) * j i + (L : ℤ) =
      (x i + (L : ℤ)) + j i * (2 * (L : ℤ) + 1) := by ring
  rw [hrw, Int.add_mul_ediv_right _ _ hb]

@[simp] theorem bgfd_centre_zero (L : ℕ) :
    bgfdCentre (d := d) L 0 = 0 := by
  funext i
  simp [bgfdCentre]


end StatMech.FrontierA
