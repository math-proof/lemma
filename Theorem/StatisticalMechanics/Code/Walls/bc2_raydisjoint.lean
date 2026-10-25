/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccthreeaxes
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc2_rayCell_distinct_of_ne {i j : Fin d} (h : i ≠ j) {s t : ℤ} (hs : s ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t :=
  hrHD_rayPt_disjoint_of_ne h hs


theorem bc2_rayCell_distinct_of_ne' {i j : Fin d} (h : i ≠ j) {s t : ℤ} (ht : t ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t :=
  (hrHD_rayPt_disjoint_of_ne (Ne.symm h) ht).symm


theorem bc2_rayCell_eq_iff_origin {i j : Fin d} (h : i ≠ j) (s t : ℤ) :
    (hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0) := by
  constructor
  · intro he
    have hi := congrFun he i
    rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j t h] at hi
    have hj := congrFun he j
    rw [hrHD_rayPt_self, hrHD_rayPt_of_ne i s (Ne.symm h)] at hj
    exact ⟨hi, hj.symm⟩
  · rintro ⟨rfl, rfl⟩
    simp


end StatMech.Walls
