/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.OrderTransition.Part2
import Def.StatisticalMechanics.Code.FK.OrderContour
open Finset Set SimpleGraph Filter Topology
open scoped BigOperators NNReal

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


@[simp] theorem peierlsContourWeight_zero (q : ℝ) : peierlsContourWeight q 0 = 1 := by
  simp [peierlsContourWeight]

theorem peierlsContourWeight_nonneg {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 ≤ peierlsContourWeight q n := by
  unfold peierlsContourWeight
  positivity


theorem card_dualCircuits_qSuppressed_le {q : ℝ} (hq : 0 < q) (n : ℕ) (v : Site 2) :
    ((dualLattice.finsetWalkLength n v v).card : ℝ) / q ^ n ≤ peierlsContourWeight q n := by
  unfold peierlsContourWeight
  rw [div_pow]
  have hqn : (0 : ℝ) < q ^ n := pow_pos hq n
  have hcard : ((dualLattice.finsetWalkLength n v v).card : ℝ) ≤ (4 : ℝ) ^ n := by
    have h : (dualLattice.finsetWalkLength n v v).card ≤ 4 ^ n := card_dual_circuits_le_pow n v
    calc ((dualLattice.finsetWalkLength n v v).card : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (4 : ℝ) ^ n := by push_cast; ring
  exact (div_le_div_iff_of_pos_right hqn).mpr hcard


theorem peierlsContourRatio_lt_one {q : ℝ} (hq : 4 < q) : (4 : ℝ) / q < 1 := by
  rw [div_lt_one (by linarith)]; linarith

theorem peierlsContourRatio_nonneg {q : ℝ} (hq : 4 < q) : (0 : ℝ) ≤ 4 / q := by
  have : (0 : ℝ) < q := by linarith
  positivity


theorem peierls_summable {q : ℝ} (hq : 4 < q) :
    Summable (peierlsContourWeight q) :=
  summable_geometric_of_lt_one (peierlsContourRatio_nonneg hq) (peierlsContourRatio_lt_one hq)


theorem peierls_tsum_eq {q : ℝ} (hq : 4 < q) :
    ∑' n, peierlsContourWeight q n = q / (q - 4) := by
  unfold peierlsContourWeight
  rw [tsum_geometric_of_lt_one (peierlsContourRatio_nonneg hq) (peierlsContourRatio_lt_one hq)]
  have hq0 : (0 : ℝ) < q := by linarith
  have hqne : q ≠ 0 := by linarith
  have h4q : (1 : ℝ) - 4 / q = (q - 4) / q := by field_simp
  rw [h4q, inv_div]


end FK
end StatMech
