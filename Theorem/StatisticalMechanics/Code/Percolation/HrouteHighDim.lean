/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Percolation.HrouteHighDim
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


@[simp] lemma hrHD_rayPt_self (j : Fin d) (t : ℤ) : hrHD_rayPt j t j = t := by simp [hrHD_rayPt]

lemma hrHD_rayPt_of_ne (j : Fin d) (t : ℤ) {i : Fin d} (h : i ≠ j) : hrHD_rayPt j t i = 0 := by
  simp [hrHD_rayPt, Pi.single_eq_of_ne h]

@[simp] lemma hrHD_rayPt_zero (j : Fin d) : hrHD_rayPt j 0 = (0 : Site d) := by
  funext i; by_cases h : i = j <;> simp [hrHD_rayPt, h, Pi.single_eq_of_ne]


lemma hrHD_rayPt_eq_zero_iff (j : Fin d) (t : ℤ) : hrHD_rayPt j t = (0 : Site d) ↔ t = 0 := by
  constructor
  · intro h; have := congrFun h j; simpa using this
  · rintro rfl; simp


lemma hrHD_adj_rayPt (j : Fin d) (t : ℤ) :
    (hypercubicLattice d).Adj (hrHD_rayPt j t) (hrHD_rayPt j (t + 1)) := by
  have h := adj_update_succ (0 : Site d) j t
  have e1 : Function.update (0 : Site d) j t = hrHD_rayPt j t := by
    funext i; by_cases hij : i = j <;> simp [hij, hrHD_rayPt, Pi.single, Function.update]
  have e2 : Function.update (0 : Site d) j (t + 1) = hrHD_rayPt j (t + 1) := by
    funext i; by_cases hij : i = j <;> simp [hij, hrHD_rayPt, Pi.single, Function.update]
  rwa [e1, e2] at h


lemma hrHD_adj_origin_rayPt_one (j : Fin d) :
    (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1) := by
  have h := hrHD_adj_rayPt j 0
  simpa using h


lemma hrHD_rayPt_one_ne_of_ne {i j : Fin d} (h : i ≠ j) :
    (hrHD_rayPt i 1 : Site d) ≠ hrHD_rayPt j 1 := by
  intro he
  have hh := congrFun he i
  rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j 1 h] at hh
  exact one_ne_zero hh


lemma hrHD_rayPt_disjoint_of_ne {i j : Fin d} (h : i ≠ j) {s t : ℤ} (hs : s ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
  intro he
  have hh := congrFun he i
  rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j t h] at hh
  exact hs hh


end Percolation
end StatMech
